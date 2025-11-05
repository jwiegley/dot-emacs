#!/usr/bin/env python3
"""
Extract ALL Fastmail Sieve rules and convert to Gnus sieve parameters.
This script properly handles the complete magnitude of rules.
"""

import json
import re
from collections import defaultdict
from pathlib import Path

def quote_sexp(sexp_str):
    """Add quote to S-expression string if needed."""
    sexp_str = sexp_str.strip()
    if sexp_str.startswith('('):
        return f"'{sexp_str}"
    return sexp_str

def parse_jmapquery(jmap_text):
    """Parse jmapquery JSON into Gnus sieve test."""
    try:
        data = json.loads(jmap_text)
    except json.JSONDecodeError:
        return None

    # Simple condition
    if "from" in data:
        return f'(address "from" "{data["from"]}")'
    elif "listId" in data:
        list_id = data["listId"]
        if not list_id.startswith("<"):
            list_id = f"<{list_id}>"
        return f'(header "list-id" "{list_id}")'
    elif "subject" in data:
        subj = data["subject"].strip('"')
        return f'(header :contains "subject" "{subj}")'
    elif "fromContactGroupId" in data:
        return f';;; TODO: Contact group {data["fromContactGroupId"]} - expand manually'

    # Complex condition with operator
    if "conditions" in data:
        operator = data.get("operator", "AND")
        conditions = data["conditions"]

        # Recursively parse each condition
        parsed_conds = []
        for cond in conditions:
            if "conditions" in cond:
                # Nested condition
                nested_op = cond.get("operator", "AND")
                nested_parsed = []
                for nested_cond in cond["conditions"]:
                    if "from" in nested_cond:
                        nested_parsed.append(f'(address "from" "{nested_cond["from"]}")')
                    elif "to" in nested_cond:
                        nested_parsed.append(f'(address "to" "{nested_cond["to"]}")')
                    elif "cc" in nested_cond:
                        nested_parsed.append(f'(address "cc" "{nested_cond["cc"]}")')
                    elif "bcc" in nested_cond:
                        nested_parsed.append(f'(address "bcc" "{nested_cond["bcc"]}")')
                    elif "deliveredTo" in nested_cond:
                        nested_parsed.append(f'(header "delivered-to" "{nested_cond["deliveredTo"]}")')
                    elif "subject" in nested_cond:
                        subj = nested_cond["subject"].strip('"')
                        nested_parsed.append(f'(header :contains "subject" "{subj}")')
                    elif "body" in nested_cond:
                        body = nested_cond["body"]
                        nested_parsed.append(f'(body :contains "{body}")')

                if nested_parsed:
                    op_word = "anyof" if nested_op == "OR" else "allof"
                    # Wrap tests in a list for gnus-sieve-test
                    parsed_conds.append(f'({op_word} (' + '\n      '.join(nested_parsed) + '))')
            else:
                # Simple condition in array
                if "from" in cond:
                    parsed_conds.append(f'(address "from" "{cond["from"]}")')
                elif "subject" in cond:
                    subj = cond["subject"].strip('"')
                    parsed_conds.append(f'(header :contains "subject" "{subj}")')
                elif "body" in cond:
                    body = cond["body"]
                    parsed_conds.append(f'(body :contains "{body}")')

        if parsed_conds:
            op_word = "anyof" if operator == "OR" else "allof"
            if len(parsed_conds) == 1:
                return parsed_conds[0]
            # Wrap tests in a list for gnus-sieve-test
            return f'({op_word} (' + '\n     '.join(parsed_conds) + '))'

    return None

def extract_rules(sieve_file):
    """Extract all rules from the Sieve file."""
    with open(sieve_file, 'r') as f:
        content = f.read()

    # Find the section with jmapquery rules
    rules_section = re.search(r'### Calculate rule actions \{\{\{(.+?)### File into folder actions',
                             content, re.DOTALL)
    if not rules_section:
        print("Could not find rules section")
        return {}

    rules_text = rules_section.group(1)

    # Find all rules
    rule_pattern = re.compile(
        r'# Search: "([^"]+)"\s+'
        r'if allof\(\s*'
        r'not string :is "\${stop}" "Y",\s*'
        r'jmapquery text:\s*'
        r'(\{.+?\})\s*\.\s*'
        r'\) \{\s*'
        r'(?:if mailboxidexists "([^"]+)" \{\s*'
        r'set "([^"]+)" "Y";\s*'
        r'set "skipinbox" "Y";\s*'
        r'\}\s*)?'
        r'set "(read|deletetotrash|stop)" "Y";',
        re.DOTALL
    )

    # Organize rules by folder variable
    folder_rules = defaultdict(list)

    for match in rule_pattern.finditer(rules_text):
        search_desc = match.group(1)
        jmap_json = match.group(2)
        mailbox_id = match.group(3)
        folder_var = match.group(4)
        action = match.group(5)

        # Skip deletetotrash actions
        if action == "deletetotrash":
            continue

        if folder_var:
            # Parse the jmapquery
            parsed = parse_jmapquery(jmap_json)
            if parsed:
                folder_rules[folder_var].append({
                    'search': search_desc,
                    'test': parsed,
                    'mailbox_id': mailbox_id
                })

    return folder_rules

def generate_elisp(folder_rules):
    """Generate Emacs Lisp file with all rules."""

    # Dynamically compute folder mapping from keys
    folder_map = {}
    for key in folder_rules.keys():
        # Parse the key: L{number}_{folder_path_with_underscores}
        match = re.match(r'^L\d+_(.+)$', key)
        if match:
            folder_path_raw = match.group(1)

            # Handle special patterns:
            # - Single underscore usually becomes slash: list_misc -> list/misc
            # - Double underscore becomes slash: list_emacs_devel -> list/emacs/devel
            # - But some special cases like org_mode -> org-mode, hackage_trustees -> hackage-trustees

            # Known patterns that should use hyphens
            hyphen_patterns = [
                ('org_mode', 'org-mode'),
                ('hackage_trustees', 'hackage-trustees'),
            ]

            # Check for known hyphen patterns first
            for pattern, replacement in hyphen_patterns:
                if pattern in folder_path_raw:
                    folder_path_raw = folder_path_raw.replace(pattern, replacement)

            # Now convert remaining underscores to slashes
            folder_path = folder_path_raw.replace('_', '/')

            # For mailbox_id, we'll use a placeholder since it's not used in generation
            # If needed, this could be extracted from the rules
            mailbox_id = 'AUTO'

            folder_map[key] = (folder_path, mailbox_id)

    output = []
    output.append(';;; fastmail-sieve-rules-complete.el --- Complete Fastmail Sieve rules -*- lexical-binding: t; -*-\n')
    output.append(';; This file contains ALL rules extracted from fastmail.sieve\n')
    output.append(';; Generated automatically - do not edit manually\n\n')
    output.append('(require \'gnus-sieve)\n\n')

    for folder_var in sorted(folder_rules.keys()):
        if folder_var not in folder_map:
            continue

        folder_name, _mailbox_id = folder_map[folder_var]
        rules = folder_rules[folder_var]

        const_name = folder_var.lower().replace('_', '-')

        output.append(f';; {folder_name} - {len(rules)} rules\n')
        output.append(f'(defconst {const_name}-sieve\n')
        output.append("  (list 'anyof\n")
        output.append("        (list\n")  # Wrap all tests in a list

        for rule in rules:
            # Add comment with search description
            search_clean = rule['search'].replace('"', '\\"')
            output.append(f'         ;; {search_clean}\n')
            # Add the test - use quote for S-expressions
            test = rule['test']
            output.append(f'         {quote_sexp(test)}\n')

        output.append('         ))\n')  # Close both the inner list and outer list
        output.append(f'  "Sieve rules for INBOX.{folder_name} ({len(rules)} rules).")\n\n')

    # Add application function
    output.append(';;;###autoload\n')
    output.append('(defun fastmail-apply-complete-sieve-rules ()\n')
    output.append('  "Apply all complete Fastmail sieve rules."\n')
    output.append('  (interactive)\n')
    output.append('  (let ((mappings\n')
    output.append('         \'(')

    for folder_var in sorted(folder_rules.keys()):
        if folder_var not in folder_map:
            continue
        folder_name, _ = folder_map[folder_var]
        const_name = folder_var.lower().replace('_', '-')
        output.append(f'           ("{folder_name}" . {const_name}-sieve)\n')

    output.append('           )))\n')
    output.append('    (dolist (mapping mappings)\n')
    output.append('      (let ((group (car mapping))\n')
    output.append('            (rule-symbol (cdr mapping)))\n')
    output.append('        (when (gnus-group-entry group)\n')
    output.append('          (gnus-group-set-parameter group \'sieve (symbol-value rule-symbol))\n')
    output.append('          (message "Applied %d rules to %s" \n')
    output.append('                   (length (car (cddr (symbol-value rule-symbol))))\n')
    output.append('                   group))))\n')
    output.append('    (message "Applied complete sieve rules to all groups")))\n\n')

    output.append('(provide \'fastmail-sieve-rules-complete)\n')
    output.append(';;; fastmail-sieve-rules-complete.el ends here\n')

    return ''.join(output)

def main():
    sieve_file = Path.home() / 'dl' / 'fastmail.sieve'
    output_file = Path.home() / 'src' / 'dot-emacs' / 'lisp' / 'fastmail-sieve-rules-complete.el'

    print(f"Parsing {sieve_file}...")
    folder_rules = extract_rules(sieve_file)

    print("\nExtracted rules:")
    total = 0
    for folder_var, rules in sorted(folder_rules.items()):
        count = len(rules)
        total += count
        print(f"  {folder_var}: {count} rules")

    print(f"\nTotal rules: {total}")

    print(f"\nGenerating {output_file}...")
    elisp_code = generate_elisp(folder_rules)

    with open(output_file, 'w') as f:
        f.write(elisp_code)

    print(f"Done! Generated {len(elisp_code)} bytes")
    print(f"\nTo use: (load-file \"{output_file}\")")
    print("Then: M-x fastmail-apply-complete-sieve-rules")

if __name__ == '__main__':
    main()

# Ponytail Help

> **GPTel preset scope:** Apply this prompt only to the current invocation.
> This is a prompt preset, not a native skill: it provides no lifecycle
> activation, persistent mode or mode switching, slash command, subagent
> propagation, plugin configuration, or plugin update mechanism.

## Available presets

| GPTel prompt name | Current-invocation behavior |
|---|---|
| `ponytail` | Full-intensity lazy-senior coding: understand the real flow, then choose the smallest correct solution. |
| `ponytail-review` | Read-only diff review for removable over-engineering. |
| `ponytail-audit` | Read-only whole-repository audit, ranked by the largest removable complexity. |
| `ponytail-debt` | Harvest `ponytail:` markers into a read-only ledger report. |
| `ponytail-gain` | Show the pinned upstream benchmark card without inventing per-repository savings. |
| `ponytail-help` | Show this GPTel-specific catalog and capability boundary. |

## Availability

Select a preset by its GPTel prompt name through the configured
`gptel-prompts` interface. Each selection applies only to that invocation;
select it again when wanted.

GPTel receives no Ponytail lifecycle activation, persistent mode or mode
switching, slash commands, subagent propagation, plugin configuration, or
plugin updates from promptdeploy. Preset content changes only when a later
promptdeploy deployment updates the pinned Ponytail bundle; this help preset
cannot update it.

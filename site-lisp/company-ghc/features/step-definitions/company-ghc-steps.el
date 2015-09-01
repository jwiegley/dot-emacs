(When "^I execute company-ghc prefix command at current point$"
      (lambda ()
        (setq company-ghc-test-prefix-output (company-ghc 'prefix))))

(Then "^company-ghc prefix is\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (equal company-ghc-test-prefix-output expected))))

(Then "^company-ghc prefix is cons with \"\\(.*\\)\" and \"\\(.*\\)\"$"
      (lambda (exp-car exp-cdr)
        (should (equal company-ghc-test-prefix-output
                       (cons exp-car (read exp-cdr))))))

(Then "^company-ghc prefix stopped$"
      (lambda ()
        (should (eq company-ghc-test-prefix-output 'stop))))

(Then "^company-ghc prefix none$"
      (lambda ()
        (should (not company-ghc-test-prefix-output))))

(When "^I execute company-ghc candidates command at current point$"
      (lambda ()
        (let* ((tmp (or (company-ghc 'prefix) 'stop))
               (prefix (if (consp tmp) (car tmp) tmp)))
          (when (not (eq prefix 'stop))
            (setq company-ghc-test-candidates-output
                  (mapcar (lambda (s) (substring-no-properties s))
                          (company-ghc 'candidates prefix)))))))

(Then "^company-ghc candidates are\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (equal company-ghc-test-candidates-output (read expected)))))

(Given "^these GHC pragmas\\(?: \"\\(.+\\)\"\\|:\\)$"
       (lambda (words)
         (setq ghc-pragma-names (split-string words "[[:space:]\n]+"))))

(Given "^these GHC language extensions\\(?: \"\\(.+\\)\"\\|:\\)$"
       (lambda (words)
         (setq ghc-language-extensions (split-string words "[[:space:]\n]+"))))

(Given "^these GHC option flags\\(?: \"\\(.+\\)\"\\|:\\)$"
       (lambda (words)
         (setq ghc-option-flags (split-string words "[[:space:]\n]+"))))

(Given "^these GHC modules\\(?: \"\\(.+\\)\"\\|:\\)$"
       (lambda (words)
         (setq ghc-module-names (split-string words "[[:space:]\n]+"))))
;;
;; Given these module keywords:
;;   | module          | keywords                     |
;;   | Data.Text       | Text singleton splitOn       |
;;   | Data.ByteString | ByteString singleton splitAt |
;;
(Given "^these module keywords:$"
       (lambda (table)
         (let ((rows (cdr table)))
           (dolist (row rows)
             (set (ghc-module-symbol (car row))
                  (split-string (cadr row) "[[:space:]\n]+"))))))

;;
;; Given these imported modules:
;;   | module          | alias |
;;   | Data.Text       | T     |
;;   | Data.ByteString |       |
;;
(Given "^these imported modules:$"
       (lambda (table)
         (let ((rows (cdr table)))
           (setq company-ghc--imported-modules
                 (mapcar
                  (lambda (row)
                    (let ((mod (car row))
                          (alias (cadr row)))
                      (cons mod (if (string= alias "") nil alias))))
                  rows)))))

(Given "^the haskell buffer template$"
       (lambda ()
         (erase-buffer)
         (insert "{-# LANGUAGE OverloadedStrings #-}\n
module Main where

@IMPORT@

foo :: Int
foo = 1

main :: IO ()
main = do
   putStrLn \"Hello\"
   return ()
")))

(When "^I replace template \"\\(.+\\)\" by\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (tmpl var)
        (save-excursion
          (goto-char (point-min))
          (when (re-search-forward (concat "\\_<@" tmpl "@\\_>"))
            (delete-region (match-beginning 0) (match-end 0))
            (insert var)))))

(When "^I execute company-ghc-scan-modules$"
      (lambda ()
        (setq company-ghc-test-imported-modules (company-ghc-scan-modules))))

(Then "^scanned modules are\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (equal company-ghc-test-imported-modules (read expected)))))

(When "^I parse hoogle search results$"
      (lambda ()
        (setq company-ghc-test-hoogle-candidates-output
              (company-ghc--hoogle-parse-results))))

(Then "^hoogle search candidates are\\(?: \"\\(.*\\)\"\\|:\\)$"
      (lambda (expected)
        (should (equal (mapcar 'substring-no-properties
                               company-ghc-test-hoogle-candidates-output)
                       (read expected)))))

(require 'parse-csv)                    ; mrc/el-csv on GitHub
(require 'rx)
(require 'eieio)

(defclass tos-lot ()
  ((lot-cost)
   (lot-date)
   (lot-id)))

(defclass tos-stock ()
  ((stk-symbol)
   (stk-lot-info)))

(defclass tos-future ()
  ((fut-symbol)
   (fut-lot-info)))

(defclass tos-option-contract ()
  ((opt-underlying)
   (opt-quantity)
   (opt-classifier)
   (opt-expiration)
   (opt-expiration-note)
   (opt-strike)
   (opt-side)
   (opt-lot-info))
  "An individual options contract")

(defclass tos-option-position ()
  ((opt-pos-multiple)
   (opt-pos-contract))
  "A position in a contract, which includes a multiplier")

(defclass tos-option-strategy ()
  ((opt-strat-name)
   (opt-strat-positions))
  "A particular options strategy
Example: a BUTTERFLY with positions at multiples of 1/2/1")

(defclass tos-post ()
  ((post-instrument)
   (post-quantity)
   (post-price)))

(defclass tos-xact ()
  ((xact-account :initarg :account)
   (xact-id :initarg :id)
   (xact-type :initarg :type)
   (xact-time :initarg :time)
   (xact-desc :initarg :desc)
   (xact-fees :initarg :fees)
   (xact-commissions :initarg :commissions)
   (xact-symbol :initarg :symbol)
   (xact-action :initarg :action)       ; buy or sell
   (xact-side :initarg :side)           ; open or close
   (xact-postings :initarg :postings)))

(defconst tos-method 2)
(defconst tos-action 3)
(defconst tos-quantity 4)
(defconst tos-strategy 5)
(defconst tos-symbol 6)
(defconst tos-addendum 7)
(defconst tos-detail 8)

(defconst tos-price 15)
(defconst tos-exchange 16)

(defconst tos-adr-fee-sym 17)
(defconst tos-cash-alt-amount 18)
(defconst tos-cash-alt-sym 19)
(defconst tos-foreign-tax-witheld-sym 20)
(defconst tos-index-option-fees 21)
(defconst tos-interest-name 22)
(defconst tos-interest-instrument 23)
(defconst tos-interest-amount 24)
(defconst tos-interest-date 25)
(defconst tos-internal-transfer-amount 26)
(defconst tos-internal-transfer-sym 27)
(defconst tos-internal-transfer-option 28)
(defconst tos-mark-to-market-sym 29)
(defconst tos-mark-to-market-amount 30)
(defconst tos-off-cycle-interest-sym 31)
(defconst tos-qualified-dividend-sym 32)
(defconst tos-option-removal-kind 33)
(defconst tos-option-removal-amount 34)
(defconst tos-option-removal-symbol 35)
(defconst tos-option-removal-contract 36)
(defconst tos-security-transfer-amount 37)
(defconst tos-security-transfer-sym 38)

(defconst tos-symbol-re
  '(+ (or alnum ?/ ?:)))

(defconst tos-num-re
  '(+ (or numeric ?+ ?- ?, ?.)))

(defmacro separated-by (re sep)
  `'(and ,re
         (zero-or-more
          (and ,sep
               ,re))))

(defconst tos-option-regex
  `(and
    ;; contract size
    (group (+ (or numeric ?/)))
    blank

    ;; special annotation
    (? (and (group (or "(Weeklys)"))
            blank))

    ;; expiration
    (group
     ,(separated-by
       (and (? (and (+ numeric)
                    blank))
            (or "JAN"
                "FEB"
                "MAR"
                "APR"
                "MAY"
                "JUN"
                "JUL"
                "AUG"
                "SEP"
                "OCT"
                "NOV"
                "DEC")
            blank
            (+ numeric)
            (* (and blank
                    (or "[AM]"
                        "(Monday)"
                        "(Wednesday)"
                        "(Friday)"
                        "(Wk1)"
                        "(Wk2)"
                        "(Wk3)"
                        "(Wk4)"
                        "(Wk5)"
                        "(EOM)"))))
       (char ?/)))
    blank

    (? (and (group ?/ ,tos-symbol-re)
            blank))

    (group ,tos-num-re
           ,(cadr (macroexpand
                   `(separated-by
                     ,tos-num-re
                     (char ?/)))))
    blank

    (group ,(separated-by
             (or "CALL"
                 "PUT")
             (char ?/)))))

(defconst tos-brokerage-transaction-regex
  (macroexpand
   `(rx
     (group
      (or
       ;; trade
       (and (? (and (group
                     (or "tIP"
                         "tIPAD"
                         "KEY: Shift B"
                         "KEY: Shift S"
                         "KEY: Ctrl Shift B"
                         "KEY: Ctrl Shift S"))
                    blank))

            (group (or "BOT" "SOLD"))
            blank

            (group ,tos-num-re)
            blank

            (? (and (group
                     (or "COVERED"
                         "DIAGONAL"
                         "DBL DIAG"
                         "VERTICAL"
                         "STRADDLE"
                         "STRANGLE"))
                    blank))

            (group
             ,(cadr
               (macroexpand
                `(separated-by
                  (and
                   ,tos-symbol-re

                   (? (and blank
                           ,tos-option-regex)))
                  (char ?/)))))

            (? (and blank
                    (group
                     (or "UPON OPTION ASSIGNMENT"
                         "UPON TRADE CORRECTION"
                         "UPON BUY TRADE"
                         "UPON SELL TRADE"
                         "UPON BONDS - REDEMPTION"))))

            (? (and blank
                    ?@
                    (group ,tos-num-re)
                    ;; optional exchange info
                    (? (and blank
                            (group
                             ,(separated-by
                               (or "AMEX"
                                   "ARCA"
                                   "BATS"
                                   "BOX"
                                   "C2"
                                   "CBOE"
                                   "EDGX"
                                   "GEMINI"
                                   "ISE"
                                   "MIAX"
                                   "NASDAQ"
                                   "NYSE"
                                   "PHLX")
                               blank)))))))

       "ACH CREDIT RECEIVED"
       "ACH DEBIT RECEIVED"
       (and "ADR FEE~"
            (group ,tos-symbol-re))
       (and "CASH ALTERNATIVES INTEREST" blank
            (group ,tos-num-re) blank
            (group ,tos-symbol-re))
       "CASH MOVEMENT OF INCOMING ACCOUNT TRANSFER"
       "CLIENT REQUESTED ELECTRONIC FUNDING DISBURSEMENT (FUNDS NOW)"
       "Courtesy Credit"
       (and "FOREIGN TAX WITHHELD~"
            (group ,tos-symbol-re))
       "FREE BALANCE INTEREST ADJUSTMENT~NO DESCRIPTION"
       (and "Index Option Fees" blank
            (group (+ (or numeric ?/))))
       (and "INTEREST INCOME - SECURITIES~"
            (group (+? anything)) blank
            (group (or "CD")) blank
            (group (and ,tos-num-re "%")) blank
            (group (+ (or numeric ?/))))
       (and "INTERNAL TRANSFER BETWEEN ACCOUNTS OR ACCOUNT TYPES" blank
            (group ,tos-num-re) blank
            (group ,tos-symbol-re)
            (? (and blank
                    (group ,tos-option-regex))))
       "MARK TO THE MARKET"
       "MISCELLANEOUS JOURNAL ENTRY"
       (and (group ,tos-symbol-re) blank
            "mark to market at" blank
            (group ,tos-num-re) blank
            "official settlement price")
       (and "OFF-CYCLE INTEREST~"
            (group ,tos-symbol-re))
       (and "QUALIFIED DIVIDEND~"
            (group ,tos-symbol-re))
       "REBATE"
       (and "REMOVAL OF OPTION DUE TO" blank
            (group (or "ASSIGNMENT" "EXPIRATION")) blank
            (group ,tos-num-re) blank
            (group ,tos-symbol-re) blank
            (group ,tos-option-regex))
       "TRANSFER FROM FOREX ACCOUNT"
       (and "TRANSFER OF SECURITY OR OPTION IN" blank
            (group ,tos-num-re) blank
            (group ,tos-symbol-re))
       "TRANSFER TO FOREX ACCOUNT"
       "WIRE INCOMING"
       )))))

;; From https://www.emacswiki.org/emacs/AddCommasToNumbers
(defun add-number-grouping (number &optional separator)
  "Add commas to NUMBER and return it as a string.
    Optional SEPARATOR is the string to use to separate groups.
    It defaults to a comma."
  (let ((num (number-to-string number))
        (op (or separator ",")))
    (while (string-match "\\(.*[0-9]\\)\\([0-9][0-9][0-9].*\\)" num)
      (setq num (concat
                 (match-string 1 num) op
                 (match-string 2 num))))
    num))

(defun tos-normalize-number (str)
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (while (search-forward "," nil t)
      (delete-region (match-beginning 0) (match-end 0)))
    (buffer-string)))

(defun tos-parse-brokerage-entry (account fields)
  (let ((date (nth 0 fields))
        (time (nth 1 fields))
        (type (nth 2 fields))
        (refno (nth 3 fields))
        (desc (nth 4 fields))
        (fees (tos-normalize-number (nth 5 fields)))
        (commissions (tos-normalize-number (nth 6 fields)))
        (amount (tos-normalize-number (nth 7 fields)))
        (balance (tos-normalize-number (nth 8 fields)))
        (re (macroexpand
             `(rx (and string-start
                       (regexp ,tos-brokerage-transaction-regex)
                       string-end)))))
    ;; A time value has structure (SEC MINUTE HOUR DAY MONTH YEAR DOW DST UTCOFF)
    (let ((date-parts (mapcar #'string-to-number (split-string date "/")))
          (time-parts (mapcar #'string-to-number (split-string time ":"))))
      (setq time (encode-time (nth 2 time-parts)
                              (nth 1 time-parts)
                              (nth 0 time-parts)
                              (nth 1 date-parts)
                              (nth 0 date-parts)
                              (nth 2 date-parts))))
    (unless (string-match re desc)
      (error "Failed to parse brokerage desc: %s" desc))
    (if (match-string tos-detail desc)
        ;; it has associated details
        t
      t)
    (setq fees (string-to-number fees)
          commissions (string-to-number commissions)
          amount (+ (string-to-number amount) fees commissions))
    (make-instance 'tos-xact
                   :account account
                   :id refno
                   :type type
                   :time time
                   :desc desc
                   :fees fees
                   :commissions commissions
                   :symbol nil
                   :action nil
                   :side nil
                   :postings nil)))

(defun tos-read ()
  (interactive)
  (let ((section 'none) account)
    (while (not (or (eobp) (eq section 'end)))
      (let ((line (buffer-substring-no-properties (line-beginning-position)
                                                  (line-end-position))))
        (cond
         ((looking-at "\\s-*$"))
         ((looking-at "Account Statement for \\([0-9]+\\)")
          (setq account (match-string 1)))
         ((looking-at "Cash Balance")
          (setq section 'cash))
         ((and (eq section 'cash)
               (looking-at "DATE,")))
         ((and (eq section 'cash)
               (looking-at ",,,,TOTAL,"))
          (setq section nil))
         ((looking-at "Futures Statements")
          (setq section 'futures))
         ((and (eq section 'futures)
               (looking-at "Trade Date,")))
         ((looking-at "Forex Statements")
          (setq section 'forex))
         ((and (eq section 'forex)
               (looking-at ",Date,")))
         ((looking-at "\"Total Cash")
          (setq section 'end))
         ((eq section 'cash)
          (tos-parse-brokerage-entry account (parse-csv->list line)))
         ((eq section 'forex)
          ;; (tos-parse-forex-entry account (parse-csv->list line))
          )
         (t
          (message "Unexpected line: %s" line))))

      (forward-line 1))))

(provide 'thinkorswim)

(require 'parse-csv)                    ; mrc/el-csv on GitHub
(require 'rx)
(require 'eieio)
(require 'calc)

(defclass tos-lot ()
  ((lot-cost)
   (lot-date)
   (lot-note)))

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

(defun tos-prepare-buffer ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\\s-*\n+" nil t)
      (delete-region (match-beginning 0) (match-end 0)))
    (goto-char (point-min))
    (when (re-search-forward "^Account Order History" nil t)
      (delete-region (match-beginning 0) (point-max)))
    (whitespace-cleanup)))

(defconst tos-method 1)
(defconst tos-action 2)
(defconst tos-quantity 3)
(defconst tos-symbol 4)
(defconst tos-option-detail 5)
(defconst tos-option-size 6)
(defconst tos-option-special 7)
(defconst tos-option-expiration 8)
(defconst tos-option-strike 9)
(defconst tos-option-side 10)
(defconst tos-price 11)
(defconst tos-exchange 12)

(defconst tos-brokerage-transaction-regex
  (macroexpand
   `(rx (or
         ;; trade
         (and (? (and (group-n
                       ,tos-method
                       (or "tIP"
                           "tIPAD"
                           "KEY: Shift B"
                           "KEY: Shift S"
                           "KEY: Ctrl Shift B"
                           "KEY: Ctrl Shift S")) blank))
              (group-n ,tos-action (or "BOT +"
                                       "SOLD -"))
              (group-n ,tos-quantity (+ (or numeric ?,))) blank
              (group-n ,tos-symbol (+ (or alpha ?/))) blank
              ;; option trade
              (? (group-n
                  ,tos-option-detail
                  (and
                   ;; contract size
                   (group-n ,tos-option-size
                            (+ (or numeric ?,)))
                   blank
                   ;; special annotation
                   (? (group-n ,tos-option-special
                               (and "(Weeklys)" blank)))
                   ;; expiration
                   (group-n
                    ,tos-option-expiration
                    (and (+ numeric)
                         blank
                         (or
                          "JAN"
                          "FEB"
                          "MAR"
                          "APR"
                          "JUN"
                          "JUL"
                          "AUG"
                          "SEP"
                          "OCT"
                          "NOV"
                          "DEC")
                         blank
                         (+ numeric)
                         (? (and blank
                                 (or "[AM]")))))
                   blank
                   (group-n ,tos-option-strike
                            (+ numeric))
                   blank
                   (group-n ,tos-option-side
                            (or "CALL"
                                "PUT"))
                   blank)))
              ?@
              (group-n ,tos-price (+ (or numeric ?.)))
              ;; optional exchange info
              (? (and blank
                      (group-n
                       ,tos-exchange
                       (or "AMEX"
                           "NASDAQ"
                           "CBOE"
                           "NYSE"
                           "GEMINI"
                           "EDGX"
                           "PHLX"
                           "BATS")))))
         ;; balance interest adjustment
         ;; market to the market
         ;; courtesy credit
         ))))

(defun tos-forward-transaction ()
  (interactive)
  (re-search-forward tos-brokerage-transaction-regex)
  (message "act %s qnt %s sym %s osz %s osp %s oxp %s ost %s osd %s prc %s xch %s"
           (or (match-string tos-action) "")
           (or (match-string tos-quantity) "")
           (or (match-string tos-symbol) "")
           (or (match-string tos-option-size) "")
           (or (match-string tos-option-special) "")
           (or (match-string tos-option-expiration) "")
           (or (match-string tos-option-strike) "")
           (or (match-string tos-option-side) "")
           (or (match-string tos-price) "")
           (or (match-string tos-exchange) "")))

(defun tos-parse-brokerage-entry (account fields)
  (let ((date (nth 0 fields))
        (time (nth 1 fields))
        (type (nth 2 fields))
        (refno (nth 3 fields))
        (desc (nth 4 fields))
        (fees (nth 5 fields))
        (commissions (nth 6 fields))
        (amount (nth 7 fields))
        (balance (nth 8 fields))
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
    (while (not (eobp))
      (let ((line (buffer-substring-no-properties (line-beginning-position)
                                                  (line-end-position))))
        (cond
         ((looking-at "^Account Statement for \\([0-9]+\\).+\n")
          (setq account (match-string 1)))
         ((looking-at "^Cash Balance\n")
          (setq section 'cash))
         ((and (eq section 'cash)
               (looking-at "^DATE,.+\n")))
         ((and (eq section 'cash)
               (looking-at "^,,,,TOTAL,.+\n"))
          (setq section nil))
         ((looking-at "^Futures Statements\n")
          (setq section 'cash))
         ((looking-at "^Forex Statements\n")
          (setq section 'cash))
         ((looking-at "^\"Total Cash.+\n")
          (setq section 'end))
         ((eq section 'cash)
          (tos-parse-brokerage-entry account (parse-csv->list line)))
         (t
          (error "Unexpected line: %s" line))))
      (forward-line 1))))

(provide 'thinkorswim)

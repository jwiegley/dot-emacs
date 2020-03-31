(require 'parse-csv)                    ; mrc/el-csv on GitHub
(require 'rx)
(require 'eieio)
(require 'anaphora)
(require 'request)
(require 'url-util)
;; (require 'web-server)

(defconst tos-base-url "https://api.tdameritrade.com/v1")

(defconst tos-client-id
  (lookup-password "developer.tdameritrade.com.client-id" "jwiegley" 80))

(defvar tos-refresh-token nil)
(defvar tos-access-token nil
  "The access token, a cons cell of the form (STRING . TIME).
Access tokens are only valid for 30 minutes.")

(defconst tos-access-token-expires (* 5 60))
(defconst tos-refresh-token-expires (* 30 60))

;; (defvar tos-web-server nil)

(defun tos-authorize ()
  (interactive)
  ;; (unless tos-web-server
  ;;   (setq tos-web-server
  ;;         (ws-start
  ;;          '(((lambda (_) t) .
  ;;             (lambda (request)
  ;;               (with-slots (process) request
  ;;                 (ws-response-header process 200 '("Content-type" . "text/plain"))
  ;;                 (process-send-string process "<html><p>Hello, world!</p></html>")))))
  ;;          9595)))
  (browse-url (concat "https://auth.tdameritrade.com/auth?"
                      "response_type=code&"
                      "redirect_uri=http%3A%2F%2F127.0.0.1%3A9595&"
                      "client_id=" (url-hexify-string tos-client-id)))
  (setq tos-refresh-token
        (cdr
         (assq
          'refresh_token
          (request-response-data
           (request
             (format "%s/oauth2/token" tos-base-url)
             :sync t
             :type "POST"
             :headers
             '(("Content-Type" . "application/x-www-form-urlencoded"))
             :data
             (format
              (concat "grant_type=authorization_code&"
                      "refresh_token=&"
                      "access_type=offline&"
                      "code=%s&"
                      "client_id=%s&"
                      "redirect_uri=http%%3A%%2F%%2F127.0.0.1:9595")
              (with-temp-buffer
                (insert (read-string "URL response from tdameritrade.com: "))
                (goto-char (point-min))
                (search-forward "code=")
                (delete-region (point-min) (match-end 0))
                (buffer-string))
              (url-hexify-string tos-client-id))
             :parser 'json-read))))
        tos-access-token nil)
  (message "thinkorswim has been authorized"))

(defun tos-get-access-token ()
  (if (and tos-access-token
           (< (float-time (time-subtract (current-time) (cdr tos-access-token)))
              tos-access-token-expires))
      (car tos-access-token)
    (setq tos-access-token
          (cons
           (cdr
            (assq
             'access_token
             (request-response-data
              (request
                (format "%s/oauth2/token" tos-base-url)
                :sync t
                :type "POST"
                :headers
                '(("Content-Type" . "application/x-www-form-urlencoded"))
                :data
                (format
                 (concat "grant_type=refresh_token&"
                         "refresh_token=%s&"
                         "access_type=offline&"
                         "code=&"
                         "client_id=%s&"
                         "redirect_uri=http%%3A%%2F%%2F127.0.0.1:9595")
                 (url-hexify-string tos-refresh-token)
                 (url-hexify-string tos-client-id))
                :parser 'json-read))))
           (current-time)))
    (car tos-access-token)))

(defun tos-field (name data)
  (aif (assq name data)
      (cdr it)
    (error "Missing %s: %S" name data)))

(defsubst tos-field-opt (name data)
  (cdr (assq name data)))

(defun tos-emit (label name data)
  (awhen (tos-field-opt name data)
    (insert (format "    ; %s: %s\n" label it))))

(defun tos-download-transactions (account-id start-date)
  (interactive)
  (ignore
   (request
    (format "%s/accounts/%s/transactions" tos-base-url account-id)
    :params `(("startDate" . ,start-date))
    :headers `(("Authorization" . ,(format "Bearer %s" (tos-get-access-token))))
    :parser 'json-read
    :success
    `(lambda (&rest args)
       (with-current-buffer (generate-new-buffer "*Transactions*")
         (dolist (xact (nreverse (mapcar #'identity (plist-get args :data))))
           ;; (insert (format "%S\n" xact))
           (insert (format "%s * (%s) %s\n"
                           (format-time-string
                            "%Y/%m/%d"
                            (parse-iso8601-time-string
                             (tos-field-opt 'transactionDate xact)))
                           (tos-field-opt 'type xact)
                           (tos-field-opt 'description xact)))
           (tos-emit "OrderId" 'orderId xact)
           (tos-emit "OrderDate" 'orderDate xact)
           (awhen (tos-field-opt 'settlementDate xact)
                  (insert (format "    ; SettlementDate:: [%s]\n" it)))
           (tos-emit "TransactionId" 'transactionId xact)
           (tos-emit "ClearingReferenceNumber" 'clearingReferenceNumber xact)
           (awhen (tos-field-opt 'transactionItem xact)
                  (tos-emit "AccountId" 'accountId it)
                  (awhen (tos-field-opt 'amount it)
                         (insert (format "    ; Amount:: %s\n"
                                         (tos-add-number-grouping it))))
                  (awhen (tos-field-opt 'price it)
                         (insert (format "    ; Price:: $%s\n"
                                         (tos-add-number-grouping it nil 2))))
                  (awhen (tos-field-opt 'cost it)
                         (insert (format "    ; Cost:: $%s\n"
                                         (tos-add-number-grouping it nil 2))))
                  (tos-emit "Instruction" 'instruction it)
                  (tos-emit "PositionEffect" 'positionEffect it)
                  (awhen (tos-field-opt 'instrument it)
                         (tos-emit "AssetType" 'assetType it)
                         (tos-emit "Symbol" 'symbol it)
                         (tos-emit "CUSIP" 'cusip it)
                         (tos-emit "Underlying" 'underlyingSymbol it)
                         (tos-emit "Description" 'description it)
                         (tos-emit "ContractType" 'putCall it)))
           (let ((fees 0.0))
             (awhen (tos-field-opt 'fees xact)
                    (let ((regFee (tos-field-opt 'regFee it))
                          (commission (tos-field-opt 'commission it)))
                      (when (and regFee (> regFee 0))
                        (setq fees (+ fees regFee))
                        (insert
                         (format
                          "    (Expenses:TD:Fees)                         $%0.2f\n"
                          regFee)))
                      (when (and commission (> commission 0))
                        (setq fees (+ fees commission))
                        (insert
                         (format
                          "    (Expenses:TD:Commission)                   $%0.2f\n"
                          commission)))))
             (awhen (tos-field-opt 'transactionItem xact)
                    (let ((amount (tos-field-opt 'amount it))
                          (price (tos-field-opt 'price it)))
                      (pcase (tos-field-opt 'instruction it)
                        ("SELL" (setq amount (- amount))))
                      (awhen (tos-field-opt 'instrument it)
                             (let ((symbol (tos-field-opt 'symbol it)))
                               (pcase (tos-field-opt 'assetType it)
                                 ("EQUITY"
                                  (insert
                                   (format
                                    "    Assets:TD:%s:%-12s       %9s %s {$%s} [%s] (%s) @ $%s\n"
                                    ,account-id
                                    "Equities"
                                    (and amount
                                         (let ((num (tos-add-number-grouping amount)))
                                           (if (string-match "\\(\\.0+\\)\\'" num)
                                               (replace-match "" t t num 1)
                                             num)))
                                    (and symbol
                                         (if (string-match "\\`[A-Z]+\\'" symbol)
                                             symbol
                                           (format "\"%s\"" symbol)))
                                    (and price (tos-add-number-grouping price nil 2))
                                    (format-time-string
                                     "%Y/%m/%d"
                                     (parse-iso8601-time-string
                                      (tos-field-opt 'transactionDate xact)))
                                    (tos-field-opt 'orderId xact)
                                    (and price (tos-add-number-grouping price nil 2)))))
                                 ("OPTION"
                                  (insert
                                   (format
                                    "    Assets:TD:%s:%-12s       %9s %s {{$%s}} [%s] (%s) @ $%s\n"
                                    ,account-id
                                    "Options"
                                    (and amount
                                         (let ((num (tos-add-number-grouping amount)))
                                           (if (string-match "\\(\\.0+\\)\\'" num)
                                               (replace-match "" t t num 1)
                                             num)))
                                    (and symbol
                                         (if (string-match "\\`[A-Z]+\\'" symbol)
                                             symbol
                                           (format "\"%s\"" symbol)))
                                    (tos-add-number-grouping
                                     (abs (tos-field-opt 'netAmount xact)) nil 2)
                                    (format-time-string
                                     "%Y/%m/%d"
                                     (parse-iso8601-time-string
                                      (tos-field-opt 'transactionDate xact)))
                                    (tos-field-opt 'orderId xact)
                                    (and price (tos-add-number-grouping
                                                (* 100 price) nil 2))))))))))
             (awhen (tos-field-opt 'netAmount xact)
                    (insert (format "    Assets:TD:%s:Cash               $%s\n"
                                    ,account-id
                                    (tos-add-number-grouping it nil 2))))

             (insert ?\n)))
         (ledger-mode)
         (ledger-post-align-postings (point-min) (point-max))
         (pop-to-buffer (current-buffer)))))))

;; (let ((td-base-url "https://api.tdameritrade.com/v1")
;;       (symbol "BAC")
;;       (client-id "<id>")
;;       (access-token "<token>")
;;       )
;;   (request
;;     (format "%s/marketdata/%s/quotes" td-base-url symbol)
;;     :params `(("apikey" . ,client-id))
;;     :headers `(("Authorization" . ,(format "Bearer %s" access-token)))
;;     :parser 'json-read
;;     :success
;;     `(lambda (&rest args)
;;        (message
;;         (mapconcat
;;          #'(lambda (entry)
;;              (format "%S = %S"
;;                      (car entry)
;;                      (cdr (assq 'lastPrice (cdr entry)))))
;;          (plist-get args :data)
;;          ", ")))))

(defclass tos-date ()
  ((day :initarg :day)
   (month :initarg :month)
   (year :initarg :year)
   (annot :initarg :annot)))

(defclass tos-lot ()
  ((cost)
   (date)
   (id)))

(defclass tos-stock ()
  ((symbol)
   (lot-info)))

(defclass tos-future ()
  ((symbol)
   (lot-info)))

(defclass tos-option-contract ()
  ((underlying :initarg :underlying)
   (multiplier :initarg :multiplier)
   (classifier :initarg :classifier)
   (expiration :initarg :expiration)
   (strike :initarg :strike)
   (side :initarg :side)
   (lot-info :initarg :lot-info))
  "An individual options contract")

(defclass tos-option-position ()
  ((factor :initarg :factor :initform 1)
   (contract :initarg :contract))
  "A position in a contract, which includes a multiplier")

(defclass tos-option-strategy ()
  ((name :initarg :name)
   (positions :initarg :positions))
  "A particular options strategy
Example: a BUTTERFLY with positions at multiples of 1/2/1")

(defclass tos-post ()
  ((instrument)
   (quantity)
   (price)))

(defclass tos-xact ()
  ((account :initarg :account)
   (id :initarg :id)
   (type :initarg :type)
   (time :initarg :time)
   (desc :initarg :desc)
   (fees :initarg :fees)
   (commissions :initarg :commissions)
   (symbol :initarg :symbol)
   (action :initarg :action)       ; buy or sell
   (side :initarg :side)           ; open or close or neither
   (postings :initarg :postings)))

(defmacro tos-many-re (&rest args)
  `(rx (: (group (+ (: (* blank)
                       (| ,@args))))
          (* blank))))

(defun tos-parse-exchange ()
  (when (looking-at
         (tos-many-re
          "AMEX"
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
          "PHLX"))
    (goto-char (match-end 0))
    (match-string 1)))

(defmacro expectation (test label &rest code)
  `(if ,test
       (progn
         ,@code)
     (tos-error-here (concat "Expected " ,label))))

(defun tos-parse-price ()
  (expectation
   (looking-at "@\\s-*")
   "pricing at-sign"
   (goto-char (match-end 0)))
  (tos-parse-number))

(defun tos-parse-contract-type ()
  (expectation
   (looking-at
    (rx (: (group
            (| "CALL"
               "PUT"))
           (* blank))))
   "contract type (CALL/PUT)"
   (goto-char (match-end 0))
   (pcase (match-string 1)
     ("CALL" :call)
     ("PUT" :put))))

(defun tos-parse-contract-multiplier ()
  (expectation
   (looking-at
    (rx (: (group (+ (| numeric ?/ ?.))) (* blank))))
   "contract multiplier"
   (goto-char (match-end 0))
   (match-string 1)))

(defun tos-parse-month ()
  (when (looking-at
         (rx (: (group
                 (| "JAN"
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
                    "DEC"))
                (* blank))))
    (goto-char (match-end 0))
    (pcase (match-string 1)
      ("JAN" 1)
      ("FEB" 2)
      ("MAR" 3)
      ("APR" 4)
      ("MAY" 5)
      ("JUN" 6)
      ("JUL" 7)
      ("AUG" 8)
      ("SEP" 9)
      ("OCT" 10)
      ("NOV" 11)
      ("DEC" 12))))

(defun tos-parse-expiration-date ()
  "Parse a contract expiration date.
For futures:
  JUN 20
  JUN 20 (Wk 2)
  JUN 20 (Monday) (Wk2)
For options:
  17 JUN 20"
  (let (day month year annot)
    (aif (tos-parse-month)
        ;; futures expiration date
        (progn
          (setq month it
                year (tos-parse-number))
          (when (looking-at
                 (tos-many-re
                  "(Monday)"
                  "(Wednesday)"
                  "(Friday)"
                  "(Wk1)"
                  "(Wk2)"
                  "(Wk3)"
                  "(Wk4)"
                  "(Wk5)"
                  "(EOM)"))
            (goto-char (match-end 0))
            (setq annot (match-string 1))))
      (setq day (tos-parse-number)
            month (tos-parse-month)
            year (tos-parse-number))
      (when (looking-at (rx (: (group (| "[AM]")) (* blank))))
        (goto-char (match-end 0))
        (setq annot (match-string 1))))

    (assert (or (null day) (and (>= day 1) (<= day 31))))
    (assert (and (>= year 19) (<= year 99)))

    (make-instance 'tos-date
                   :day day
                   :month month
                   :year (+ year 2000)
                   :annot annot)))

(defun tos-error-here (label)
  (error "%s: %s" label (buffer-substring-no-properties
                         (point) (line-end-position))))

(defun tos-parse-symbol ()
  (expectation
   (looking-at
    (rx (: (group (? ?/) (+ (| alnum ?:))) (* blank))))
   "symbol"
   (goto-char (match-end 0))
   (match-string 1)))

(defun tos-parse-instrument ()
  "Parse an investment instrument being traded.
Possibilities:
- An equity, such as stock, etf, CDs, etc.
- A futures contract
- A futures spread
- An options contract on equities or futures, etc.
- An options strategy involving multiple contracts"
  (let (symbol strategy multipier annot expiration strike contract-type)
    (when (looking-at
           (rx (: (group
                   (| "COVERED"
                      "DIAGONAL"
                      "DBL DIAG"
                      "VERTICAL"
                      "STRADDLE"
                      "STRANGLE"))
                  (* blank))))
      (goto-char (match-end 0))
      (setq strategy (match-string 1)))
    (setq symbol (tos-parse-symbol))
    (awhen (tos-parse-contract-multiplier)
      (setq multipier it)
      (when (looking-at
             (rx (: (group
                     (| "(Weeklys)"))
                    (* blank))))
        (goto-char (match-end 0))
        (setq annot (match-string 1)))
      (setq expiration (tos-parse-expiration-date)
            strike (tos-parse-number)
            contract-type (tos-parse-contract-type)))
    (if multipier
        (make-instance
         'tos-option-strategy
         :name strategy
         :positions
         (list (make-instance
                'tos-option-position
                :factor 1
                :contract
                (make-instance
                 'tos-option-contract
                 :underlying symbol
                 :multiplier multipier
                 :classifier annot
                 :expiration expiration
                 :strike strike
                 :side contract-type
                 :lot-info nil)))))))

(defun tos-normalize-number (str)
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (while (search-forward "," nil t)
      (delete-region (match-beginning 0) (match-end 0)))
    (buffer-string)))

(defun tos-parse-number ()
  "Parse numbers like -1,790.38 or +200 or just 30."
  (expectation
   (looking-at
    (rx (: (group (? (| ?- ?+))
                  (* (| numeric ?,))
                  (* (| numeric ?.)))
           (* blank))))
   "amount"
   (goto-char (match-end 0))
   (string-to-number (tos-normalize-number (match-string 1)))))

(defun tos-parse-action ()
  (when (looking-at
         (rx (: (| "tIP"
                   "tIPAD"
                   "KEY: Shift B"
                   "KEY: Shift S"
                   "KEY: Ctrl Shift B"
                   "KEY: Ctrl Shift S")
                blank)))
    (goto-char (match-end 0)))
  (expectation
   (looking-at
    (rx (: (group
            (| "BOT"
               "SOLD"))
           (* blank))))
   "action (BOT/SOLD)"
   (goto-char (match-end 0))
   (pcase (match-string 1)
     ("BOT" :buy)
     ("SOLD" :sell))))

(defun tos-parse-buy/sell-transaction ()
  (awhen (ignore-errors (tos-parse-action))
    (let ((action it)
          quantity instrument price exchange)
      (setq quantity (tos-parse-number)
            instrument (tos-parse-instrument)
            price (tos-parse-price)
            exchange (tos-parse-exchange))
      (list quantity instrument price exchange))))

(defun tos-parse-transaction-description ()
  (acond
   ((looking-at "ACH CREDIT RECEIVED"))
   ((looking-at "ACH DEBIT RECEIVED"))
   ((looking-at "ADR FEE~")
    (goto-char (match-end 0))
    (tos-parse-symbol))
   ((looking-at "CASH ALTERNATIVES INTEREST")
    (goto-char (match-end 0))
    (tos-parse-number)
    (tos-parse-symbol))
   ((looking-at "CASH MOVEMENT OF INCOMING ACCOUNT TRANSFER"))
   ((looking-at "CLIENT REQUESTED ELECTRONIC FUNDING DISBURSEMENT (FUNDS NOW)"))
   ((looking-at "Courtesy Credit"))
   ((looking-at "FOREIGN TAX WITHHELD~")
    (goto-char (match-end 0))
    (tos-parse-symbol))
   ((looking-at "FREE BALANCE INTEREST ADJUSTMENT~NO DESCRIPTION"))
   ((looking-at "Index Option Fees\\s-+")
    (goto-char (match-end 0))
    (tos-parse-contract-multiplier))
   ((looking-at "INTEREST INCOME - SECURITIES~")
    (goto-char (match-end 0))
    (looking-at
     (rx (: (group (+? anything)) blank
            (group (or "CD")) blank
            (group (and (+ numeric) "%")) blank
            (group (+ (or numeric ?/)))))))
   ((looking-at "INTERNAL TRANSFER BETWEEN ACCOUNTS OR ACCOUNT TYPES\\s-+")
    (goto-char (match-end 0))
    (tos-parse-number)
    (tos-parse-instrument))
   ((looking-at "MARK TO THE MARKET"))
   ((looking-at "MISCELLANEOUS JOURNAL ENTRY"))
   ((looking-at "OFF-CYCLE INTEREST~")
    (goto-char (match-end 0))
    (tos-parse-symbol))
   ((looking-at "QUALIFIED DIVIDEND~")
    (goto-char (match-end 0))
    (tos-parse-symbol))
   ((looking-at "REBATE"))
   ((looking-at "REMOVAL OF OPTION DUE TO\\s-+")
    (goto-char (match-end 0))
    (looking-at (rx (: (group (| "ASSIGNMENT" "EXPIRATION"))
                       (* blank))))
    (goto-char (match-end 0))
    (tos-parse-number)
    (tos-parse-instrument))
   ((looking-at "TRANSFER FROM FOREX ACCOUNT"))
   ((looking-at "TRANSFER OF SECURITY OR OPTION IN\\s-+")
    (goto-char (match-end 0))
    (tos-parse-number)
    (tos-parse-symbol))
   ((looking-at "TRANSFER TO FOREX ACCOUNT"))
   ((looking-at "WIRE INCOMING"))

   ((ignore-errors (tos-parse-action))
    (let ((action it)
          quantity instrument price exchange)
      (setq quantity (tos-parse-number)
            instrument (tos-parse-instrument)
            price (tos-parse-price)
            exchange (tos-parse-exchange))))

   ((ignore-errors (tos-parse-symbol))
    (let ((symbol it)
          price)
      (looking-at "mark to market at\\s-+")
      (setq price (tos-parse-number))
      (looking-at "official settlement price\\s-*")))

   (t
    (tos-error-here "Unrecognized transaction description"))))

;; (defmacro separated-by (re sep)
;;   `'(and ,re
;;          (zero-or-more
;;           (and ,sep
;;                ,re))))

;; (defconst tos-option-regex
;;   `(and
;;     ;; contract size
;;     (group (+ (or numeric ?/)))
;;     blank

;;     ;; special annotation
;;     (? (and (group (or "(Weeklys)"))
;;             blank))

;;     ;; expiration
;;     (group
;;      ,(separated-by
;;        (and (? (and (+ numeric)
;;                     blank))
;;             (or "JAN"
;;                 "FEB"
;;                 "MAR"
;;                 "APR"
;;                 "MAY"
;;                 "JUN"
;;                 "JUL"
;;                 "AUG"
;;                 "SEP"
;;                 "OCT"
;;                 "NOV"
;;                 "DEC")
;;             blank
;;             (+ numeric)
;;             (* (and blank
;;                     (or "[AM]"
;;                         "(Monday)"
;;                         "(Wednesday)"
;;                         "(Friday)"
;;                         "(Wk1)"
;;                         "(Wk2)"
;;                         "(Wk3)"
;;                         "(Wk4)"
;;                         "(Wk5)"
;;                         "(EOM)"))))
;;        (char ?/)))
;;     blank

;;     (? (and (group ?/ ,tos-symbol-re)
;;             blank))

;;     (group ,tos-num-re
;;            ,(cadr (macroexpand
;;                    `(separated-by
;;                      ,tos-num-re
;;                      (char ?/)))))
;;     blank

;;     (group ,(separated-by
;;              (or "CALL"
;;                  "PUT")
;;              (char ?/)))))

;; (defconst tos-brokerage-transaction-regex
;;   (macroexpand
;;    `(rx
;;      (group
;;       (or
;;        ;; trade
;;        (and (? (and (group
;;                      (or "tIP"
;;                          "tIPAD"
;;                          "KEY: Shift B"
;;                          "KEY: Shift S"
;;                          "KEY: Ctrl Shift B"
;;                          "KEY: Ctrl Shift S"))
;;                     blank))

;;             (group (or "BOT" "SOLD"))
;;             blank

;;             (group ,tos-num-re)
;;             blank

;;             (? (and (group
;;                      (or "COVERED"
;;                          "DIAGONAL"
;;                          "DBL DIAG"
;;                          "VERTICAL"
;;                          "STRADDLE"
;;                          "STRANGLE"))
;;                     blank))

;;             (group
;;              ,(cadr
;;                (macroexpand
;;                 `(separated-by
;;                   (and
;;                    ,tos-symbol-re

;;                    (? (and blank
;;                            ,tos-option-regex)))
;;                   (char ?/)))))

;;             (? (and blank
;;                     (group
;;                      (or "UPON OPTION ASSIGNMENT"
;;                          "UPON TRADE CORRECTION"
;;                          "UPON BUY TRADE"
;;                          "UPON SELL TRADE"
;;                          "UPON BONDS - REDEMPTION"))))

;;             (? (and blank
;;                     ?@
;;                     (group ,tos-num-re)
;;                     ;; optional exchange info
;;                     (? (and blank
;;                             (group
;;                              ,(separated-by
;;                                (or "AMEX"
;;                                    "ARCA"
;;                                    "BATS"
;;                                    "BOX"
;;                                    "C2"
;;                                    "CBOE"
;;                                    "EDGX"
;;                                    "GEMINI"
;;                                    "ISE"
;;                                    "MIAX"
;;                                    "NASDAQ"
;;                                    "NYSE"
;;                                    "PHLX")
;;                                blank)))))))

;;        "ACH CREDIT RECEIVED"
;;        "ACH DEBIT RECEIVED"
;;        (and "ADR FEE~"
;;             (group ,tos-symbol-re))
;;        (and "CASH ALTERNATIVES INTEREST" blank
;;             (group ,tos-num-re) blank
;;             (group ,tos-symbol-re))
;;        "CASH MOVEMENT OF INCOMING ACCOUNT TRANSFER"
;;        "CLIENT REQUESTED ELECTRONIC FUNDING DISBURSEMENT (FUNDS NOW)"
;;        "Courtesy Credit"
;;        (and "FOREIGN TAX WITHHELD~"
;;             (group ,tos-symbol-re))
;;        "FREE BALANCE INTEREST ADJUSTMENT~NO DESCRIPTION"
;;        (and "Index Option Fees" blank
;;             (group (+ (or numeric ?/))))
;;        (and "INTEREST INCOME - SECURITIES~"
;;             (group (+? anything)) blank
;;             (group (or "CD")) blank
;;             (group (and ,tos-num-re "%")) blank
;;             (group (+ (or numeric ?/))))
;;        (and "INTERNAL TRANSFER BETWEEN ACCOUNTS OR ACCOUNT TYPES" blank
;;             (group ,tos-num-re) blank
;;             (group ,tos-symbol-re)
;;             (? (and blank
;;                     (group ,tos-option-regex))))
;;        "MARK TO THE MARKET"
;;        "MISCELLANEOUS JOURNAL ENTRY"
;;        (and (group ,tos-symbol-re) blank
;;             "mark to market at" blank
;;             (group ,tos-num-re) blank
;;             "official settlement price")
;;        (and "OFF-CYCLE INTEREST~"
;;             (group ,tos-symbol-re))
;;        (and "QUALIFIED DIVIDEND~"
;;             (group ,tos-symbol-re))
;;        "REBATE"
;;        (and "REMOVAL OF OPTION DUE TO" blank
;;             (group (or "ASSIGNMENT" "EXPIRATION")) blank
;;             (group ,tos-num-re) blank
;;             (group ,tos-symbol-re) blank
;;             (group ,tos-option-regex))
;;        "TRANSFER FROM FOREX ACCOUNT"
;;        (and "TRANSFER OF SECURITY OR OPTION IN" blank
;;             (group ,tos-num-re) blank
;;             (group ,tos-symbol-re))
;;        "TRANSFER TO FOREX ACCOUNT"
;;        "WIRE INCOMING"
;;        )))))

;; From s.el
(defun tos-pad-right (len padding s)
  "If S is shorter than LEN, pad it with PADDING on the right."
  (declare (pure t) (side-effect-free t))
  (let ((extra (max 0 (- len (length s)))))
    (concat s
            (make-string extra (string-to-char padding)))))

;; From https://www.emacswiki.org/emacs/AddCommasToNumbers
(defun tos-add-number-grouping (number &optional separator precision)
  "Add commas to NUMBER and return it as a string.
    Optional SEPARATOR is the string to use to separate groups.
    It defaults to a comma."
  (let* ((str (number-to-string number))
         (op (or separator ","))
         (parts (split-string str "\\."))
         (num (nth 0 parts))
         (rem (nth 1 parts)))
    (while (string-match "\\(.*[0-9]\\)\\([0-9][0-9][0-9].*\\)" num)
      (setq num (concat
                 (match-string 1 num) op
                 (match-string 2 num))))
    (if rem
        (progn
          (setq num (concat num "." (if precision
                                        (tos-pad-right precision "0" rem)
                                      rem))))
      num)))

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

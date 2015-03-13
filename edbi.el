;;; edbi.el --- Database independent interface for Emacs

;; Copyright (C) 2011, 2012  SAKURAI Masashi

;; Author: SAKURAI Masashi <m.sakurai at kiwanami.net>
;; Version: 0.1.1
;; Keywords: database, epc
;; URL: https://github.com/kiwanami/emacs-edbi

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This program connects the database server through Perl's DBI,
;; and provides DB-accessing API and the simple management UI.

;;; Installation:

;; This program depends on following programs:
;;  - deferred.el, concurrent.el / https://github.com/kiwanami/emacs-deferred
;;  - epc.el      / https://github.com/kiwanami/emacs-epc
;;  - ctable.el   / https://github.com/kiwanami/emacs-ctable
;;  - Perl/CPAN
;;    - RPC::EPC::Service (and some dependent modules)
;;    - DBI and drivers, DBD::Sqlite, DBD::Pg, DBD::mysql

;; Place this program (edbi.el and edbi-bridge.pl) in your load path
;; and add following code.

;; (require 'edbi)

;; Then,  M-x `edbi:open-db-viewer' opens a dialog for DB connection.
;; - Data Source : URI string for DBI::connect (Ex. dbi:SQLite:dbname=/path/db.sqlite )
;; - User Name, Auth : user name and password for DBI::connect
;; - History button : you can choose a data source from your connection history.
;; - OK button : connect DB and open the database view

;; * Database view
;; This buffer enumerates tables and views.
;; Check the key-bind `edbi:dbview-keymap'.
;; - j,k, n,p : navigation for rows
;; - c        : switch to query editor buffer
;; - RET      : show table data
;; - SPC      : show table definition
;; - q        : quit and disconnect

;; * Table definition view
;; This buffer shows the table definition information.
;; Check the key-bind `edbi:dbview-table-keymap'.
;; - j,k, n,p : navigation for rows
;; - c        : switch to query editor buffer
;; - V        : show table data
;; - q        : kill buffer

;; * Query editor
;; You can edit SQL in this buffer, which supports SQL syntax
;; highlight and auto completion by auto-complete.el.
;; Check the key-bind `edbi:sql-mode-map'.
;; - C-c C-c  : Execute SQL
;; - C-c q    : kill buffer
;; - M-p      : SQL history back
;; - M-n      : SQL history forward
;; - C-c C-k  : Clear buffer

;; * Query result viewer
;; You can browser the results for executed SQL.
;; Check the key-bind `edbi:dbview-query-result-keymap'.
;; - j,k, n,p : navigation for rows
;; - q        : kill buffer


;;; Code:


(eval-when-compile (require 'cl))
(require 'epc)
(require 'sql)

;;; Configurations

(defvar edbi:driver-libpath (file-name-directory (or load-file-name ".")) 
  "directory for the driver program.")

(defvar edbi:driver-info (list "perl" 
                               (expand-file-name 
                                "edbi-bridge.pl" 
                                edbi:driver-libpath))
  "driver program info.")


;;; Utility

(defmacro edbi:seq (first-d &rest elements)
  "Deferred sequence macro."
  (let* ((pit 'it)
         (vsym (gensym))
         (fs 
          (cond
           ((eq '<- (nth 1 first-d))
            (let ((var (car first-d)) (f (nth 2 first-d)))
              `(deferred:nextc ,f
                 (lambda (,vsym) (setq ,var ,vsym)))))
           (t first-d)))
         (ds (loop for i in elements
                   collect
                   (cond
                    ((eq 'lambda (car i))
                     `(deferred:nextc ,pit ,i))
                    ((eq '<- (nth 1 i))
                     (let ((var (car i)) (f (nth 2 i)))
                     `(deferred:nextc ,pit 
                        (lambda (x) 
                          (deferred:$ ,f
                            (deferred:nextc ,pit
                              (lambda (,vsym) (setq ,var ,vsym))))))))
                    (t
                     `(deferred:nextc ,pit (lambda (x) ,i)))))))
    `(deferred:$ ,fs ,@ds)))

(defmacro edbi:liftd (f deferred)
  "Deferred function utility, like liftM."
  (let ((vsym (gensym)))
    `(deferred:nextc ,deferred
       (lambda (,vsym) (,f ,vsym)))))

(defmacro edbi:sync (fsym conn &rest args)
  "Synchronous calling wrapper macro. FSYM is deferred function in the edbi."
  `(epc:sync (edbi:connection-mngr ,conn) (,fsym ,conn ,@args)))

(defun edbi:column-selector (columns name)
  "[internal] Return a column selector function."
  (lexical-let (num)
    (or
     (loop for c in columns
           for i from 0
           if (equal c name)
           return (progn 
                    (setq num i)
                    (lambda (xs) (nth num xs))))
     (lambda (xs) nil))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Low level API

;; data types

(defun edbi:data-source (uri &optional username auth)
  "Create data source object."
  (list uri username auth))

(defun edbi:data-source-uri (data-source)
  "Return the uri slot of the DATA-SOURCE."
  (car data-source))

(defun edbi:data-source-username (data-source)
  "Return the username slot of the DATA-SOURCE."
  (nth 1 data-source))

(defun edbi:data-source-auth (data-source)
  "Return the auth slot of the DATA-SOURCE."
  (nth 2 data-source))

(defstruct edbi:ac-candidates tables columns types keywords)

(defun edbi:connection (epc-mngr)
  "Create an `edbi:connection' object."
  ;; edbi:manager, edbi:data-source, query-buffers, ac-sources
  (list epc-mngr nil nil nil))

(defsubst edbi:connection-mngr (conn)
  "Return the `epc:manager' object."
  (car conn))

(defsubst edbi:connection-ds (conn)
  "Return the `edbi:data-source' object."
  (nth 1 conn))

(defun edbi:connection-ds-set (conn ds)
  "[internal] Store data-source object at CONN object."
  (if (nth 1 conn) (error "BUG: Data Source object is set unexpectedly.")
    (setf (nth 1 conn) ds)))

(defun edbi:connection-buffers (conn)
  "Return the buffer list of query editors."
  (let ((buf-list (nth 2 conn)))
    (setq buf-list
          (loop for i in buf-list
                if (buffer-live-p i)
                collect i))
    (setf (nth 2 conn) buf-list)
    buf-list))

(defun edbi:connection-buffers-set (conn buffer-list)
  "[internal] Store BUFFER-LIST at CONN object."
  (setf (nth 2 conn) buffer-list))

(defun edbi:connection-ac (conn)
  "Return ac-candidate object."
  (nth 3 conn))

(defun edbi:connection-ac-set (conn ac-candidate)
  "[internal] Store ac-candidate object at CONN object."
  (setf (nth 3 conn) ac-candidate))


;; API

(defun edbi:start ()
  "Start the EPC process. This function returns an `edbi:connection' object.
The functions `edbi:start' and `edbi:connect' are separated so as
for library users to inspect where the problem is occurred. If
`edbi:start' is failed, the EPC peer process may be wrong. If
`edbi:connect' is failed, the DB setting or environment is
wrong."
  (edbi:connection
   (epc:start-epc (car edbi:driver-info) (cdr edbi:driver-info))))

(defun edbi:finish (conn)
  "Terminate the EPC process."
  (epc:stop-epc (edbi:connection-mngr conn)))


(defun edbi:connect (conn data-source)
  "Connect to the DB. DATA-SOURCE is a `edbi:data-source' object.
This function executes peer's API synchronously.
This function returns the value of '$dbh->get_info(18)' which
shows the DB version string. (Some DB may return nil.)"
  (let ((mngr (edbi:connection-mngr conn)))
    (prog1
        (epc:call-sync mngr 'connect 
                       (list (edbi:data-source-uri data-source)
                             (edbi:data-source-username data-source)
                             (edbi:data-source-auth data-source)))
      (edbi:connection-ds-set conn data-source)
      (setf (epc:manager-title mngr) (edbi:data-source-uri data-source)))))

(defun edbi:do-d (conn sql &optional params)
  "Execute SQL and return a number of affected rows."
  (epc:call-deferred 
   (edbi:connection-mngr conn) 'do (cons sql params)))

(defun edbi:select-all-d (conn sql &optional params)
  "Execute the query SQL and returns all result rows."
  (epc:call-deferred 
   (edbi:connection-mngr conn) 'select-all (cons sql params)))

(defun edbi:prepare-d (conn sql)
  "[STH] Prepare the statement for SQL. 
This function holds the statement as a state in the edbi-bridge. 
The programmer should be aware of the internal state so as not to break the state."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'prepare sql))

(defun edbi:execute-d (conn &optional params)
  "[STH] Execute the statement."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'execute params))

(defun edbi:fetch-columns-d (conn)
  "[STH] Fetch a list of the column titles."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'fetch-columns nil))

(defun edbi:fetch-d (conn &optional num)
  "[STH] Fetch a row object. NUM is a number of retrieving rows. If NUM is nil, this function retrieves all rows."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'fetch num))

(defun edbi:auto-commit-d (conn flag)
  "Set the auto-commit flag. FLAG is 'true' or 'false' string."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'auto-commit flag))

(defun edbi:commit-d (conn)
  "Commit transaction."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'commit nil))

(defun edbi:rollback-d (conn)
  "Rollback transaction."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'rollback nil))

(defun edbi:disconnect-d (conn)
  "Close the DB connection."
  (epc:stop-epc conn))

(defun edbi:status-info-d (conn)
  "Return a list of `err' code, `errstr' and `state'."
  (epc:call-deferred (edbi:connection-mngr conn) 'status nil))

(defun edbi:type-info-all-d (conn)
  "Return a list of type info."
  (epc:call-deferred (edbi:connection-mngr conn) 'type-info-all nil))

(defun edbi:table-info-d (conn catalog schema table type)
  "Return a table info as (COLUMN-LIST ROW-LIST)."
  (epc:call-deferred 
   (edbi:connection-mngr conn) 'table-info (list catalog schema table type)))

(defun edbi:column-info-d (conn catalog schema table column)
  "Return a column info as (COLUMN-LIST ROW-LIST)."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'column-info (list catalog schema table column)))

(defun edbi:primary-key-info-d (conn catalog schema table)
  "Return a primary key info as (COLUMN-LIST ROW-LIST)."
  (epc:call-deferred
   (edbi:connection-mngr conn) 'primary-key-info (list catalog schema table)))

(defun edbi:foreign-key-info-d (conn pk-catalog pk-schema pk-table 
                                   fk-catalog fk-schema fk-table)
  "Return a foreign key info as (COLUMN-LIST ROW-LIST)."
  (epc:call-deferred (edbi:connection-mngr conn) 'foreign-key-info
                     (list pk-catalog pk-schema pk-table 
                           fk-catalog fk-schema fk-table)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DB Driver Abstraction

;; [edbi:dbd structure]
;;
;;   name               : driver name
;;   table-info-args    : a function that receives an `edbi:connection' object 
;;                        and returns a list for the arguments of `edbi:table-info-d'.
;;   table-info-filter  : a function that receives the return value of `edbi:table-info-d' 
;;                        and returns a filtered list (catalog schema table-name type remarks).
;;   column-info-args   : argument function for `edbi:column-info-d'.
;;   column-info-filter : filter function for `edbi:column-info-d'.
;;                        this function returns a list of 
;;                        (table-name column-name type-name column-size nullable remarks)
;;   type-info-filter   : filter function for `edbi:type-info-all-d'.
;;                        this function returns a list of type-name.
;;   limit-format       : a format string for the limited select statement.
;;   keywords           : return a SQL keywords function
;;
;; TODO: collectiong indexes

(defstruct edbi:dbd name table-info-args table-info-filter
  column-info-args column-info-filter type-info-filter limit-format keywords)

(defvar edbi:dbd-alist nil "[internal] List of the dbd name and `edbi:dbd' object.")
(defvar edbi:dbd-default nil "[internal] Default `edbi:dbd' object.")

(defun edbi:dbd-register (dbd)
  "Register the `edbi:dbd' object to `edbi:dbd-alist'."
  (let ((name (edbi:dbd-name dbd)))
    (setq edbi:dbd-alist 
          (loop for i in edbi:dbd-alist
                unless (equal (car i) name) collect i))
    (push (cons name dbd) edbi:dbd-alist))
  edbi:dbd-alist)

(defun edbi:dbd-get (conn)
  "[internal] Return the `edbi:dbd' object for CONN."
  (let* ((uri (edbi:data-source-uri (edbi:connection-ds conn)))
         (ps (string-match "^dbi:[^:]+" uri)) ret)
    (when ps
      (let ((name (match-string 0 uri)))
        (setq ret (cdr (assoc name edbi:dbd-alist)))))
    (unless ret
      (setq ret edbi:dbd-default))
    ret))

(defun edbi:dbd-extract-table-info (table-info)
  "[internal] Extract TABLE-INFO as follows:

  ((CATALOG SCHEMA TABLE TYPE REMARKS) ...)"
  (loop 
   with hrow = (and table-info (car table-info))
   with rows = (and table-info (cadr table-info))
   with catalog-f = (edbi:column-selector hrow "TABLE_CAT")
   with schema-f  = (edbi:column-selector hrow "TABLE_SCHEM")
   with table-f   = (edbi:column-selector hrow "TABLE_NAME")
   with type-f    = (edbi:column-selector hrow "TABLE_TYPE")
   with remarks-f = (edbi:column-selector hrow "REMARKS")
   for row in rows
   for catalog = (funcall catalog-f row)
   for schema  = (funcall schema-f row)
   for type    = (or (funcall type-f row) "")
   for table   = (funcall table-f row)
   for remarks = (or (funcall remarks-f row) "")
   if table
   collect (list catalog schema table type remarks)))

(defun edbi:dbd-default-table-info-filter (table-info)
  "[internal] Default table name filter."
  (loop for rec in (edbi:dbd-extract-table-info table-info)
        for (catalog schema table type remarks) = rec
        if (not (or (string-match "\\(INDEX\\|SYSTEM\\)" type)
                    (string-match "\\(information_schema\\|SYSTEM\\)" schema)))
        collect rec))

(defun edbi:dbd-extract-column-info (column-info)
  "[internal] Extract COLUMN-INFO as follows:

  ((TABLE-NAME COLUMN-NAME TYPE-NAME COLUMN-SIZE NULLABLE REMARKS)...)"
  (loop
   with hrow = (and column-info (car column-info))
   with rows = (and column-info (cadr column-info))
   with table-name-f  = (edbi:column-selector hrow "TABLE_NAME")
   with column-name-f = (edbi:column-selector hrow "COLUMN_NAME")
   with type-name-f   = (edbi:column-selector hrow "TYPE_NAME")
   with column-size-f = (edbi:column-selector hrow "COLUMN_SIZE")
   with nullable-f    = (edbi:column-selector hrow "NULLABLE")
   with remarks-f     = (edbi:column-selector hrow "REMARKS")
   for row in rows
   for table-name  = (funcall table-name-f row)
   for column-name = (funcall column-name-f row)
   for type-name   = (funcall type-name-f row)
   for column-size = (or (funcall column-size-f row) "")
   for nullable    = (if (equal 0 (funcall nullable-f row)) "NOT NULL" "")
   for remarks     = (or (funcall remarks-f row) "")
   if column-name
   collect (list table-name column-name type-name column-size nullable remarks)))

(defun edbi:dbd-default-column-info-filter (column-info)
  "[internal] Default column name filter."
  (edbi:dbd-extract-column-info column-info))

(defun edbi:dbd-default-type-info-filter (type-info)
  "[internal] Default type info filter."
  (let (ret)
    (when type-info
      (let ((name-col
             (loop for (n . i) in (car type-info)
                   if (equal n "TYPE_NAME") return i)))
        (when name-col
          (setq ret
                (loop for type-row in (cdr type-info)
                      for name = (nth name-col type-row)
                      collect 
                      (cons (propertize name 'summary "TYPE") name))))))
    (unless ret
      ;; fallback : enumerate well known types
      (setq ret (list "INT" "INTEGER" "TINYINT" "SMALLINT" "MEDIUMINT" 
                      "BIGINT" "UNSIGNED" "BIG" "INTEGER" "CHARACTER"
                      "VARCHAR" "NCHAR" "NVARCHAR" "CLOB" "TEXT" "BLOB"
                      "REAL" "DOUBLE" "FLOAT" "NUMERIC" "DECIMAL" "BOOLEAN"
                      "DATE" "DATETIME")))
    ret))

(defun edbi:dbd-default-keywords ()
  "[internal] Default SQL keywords, following format:
 (list (\"keyword type\" . (keyword list)) ... )"
  (list
   (cons "Keyword"
         (list
          "ABSOLUTE" "ACTION" "ADD" "ADMIN" "AFTER" "AGGREGATE" "ALIAS" "ALL"
          "ALLOCATE" "ALTER" "AND" "ANY" "ARE" "AS" "ASC" "ASSERTION" "AT"
          "AUTHORIZATION" "BEFORE" "BEGIN" "BOTH" "BREADTH" "BY" "CALL"
          "CASCADE" "CASCADED" "CASE" "CATALOG" "CHECK" "CLASS" "CLOSE"
          "COLLATE" "COLLATION" "COLUMN" "COMMIT" "COMPLETION" "CONNECT"
          "CONNECTION" "CONSTRAINT" "CONSTRAINTS" "CONSTRUCTOR" "CONTINUE"
          "CORRESPONDING" "CREATE" "CROSS" "CUBE" "CURRENT" "CURSOR" "CYCLE"
          "DATA" "DAY" "DEALLOCATE" "DECLARE" "DEFAULT" "DEFERRABLE" "DEFERRED"
          "DELETE" "DEPTH" "DEREF" "DESC" "DESCRIBE" "DESCRIPTOR" "DESTROY"
          "DESTRUCTOR" "DETERMINISTIC" "DIAGNOSTICS" "DICTIONARY" "DISCONNECT"
          "DISTINCT" "DOMAIN" "DROP" "DYNAMIC" "EACH" "ELSE" "END" "EQUALS"
          "ESCAPE" "EVERY" "EXCEPT" "EXCEPTION" "EXEC" "EXECUTE" "EXTERNAL"
          "FALSE" "FETCH" "FIRST" "FOR" "FOREIGN" "FOUND" "FREE" "FROM" "FULL"
          "FUNCTION" "GENERAL" "GET" "GLOBAL" "GO" "GOTO" "GRANT" "GROUP"
          "GROUPING" "HAVING" "HOST" "HOUR" "IDENTITY" "IGNORE" "IMMEDIATE" "IN"
          "INDICATOR" "INITIALIZE" "INITIALLY" "INNER" "INOUT" "INPUT" "INSERT"
          "INTERSECT" "INTO" "IS" "ISOLATION" "ITERATE" "JOIN" "KEY" "LANGUAGE"
          "LAST" "LATERAL" "LEADING" "LEFT" "LESS" "LEVEL" "LIKE" "LIMIT"
          "LOCAL" "LOCATOR" "MAP" "MATCH" "MINUTE" "MODIFIES" "MODIFY" "MODULE"
          "MONTH" "NAMES" "NATURAL" "NEW" "NEXT" "NO" "NONE" "NOT" "NULL" "OF"
          "OFF" "OLD" "ON" "ONLY" "OPEN" "OPERATION" "OPTION" "OR" "ORDER"
          "ORDINALITY" "OUT" "OUTER" "OUTPUT" "PAD" "PARAMETER" "PARAMETERS"
          "PARTIAL" "PATH" "POSTFIX" "PREFIX" "PREORDER" "PREPARE" "PRESERVE"
          "PRIMARY" "PRIOR" "PRIVILEGES" "PROCEDURE" "PUBLIC" "READ" "READS"
          "RECURSIVE" "REFERENCES" "REFERENCING" "RELATIVE" "RESTRICT" "RESULT"
          "RETURN" "RETURNS" "REVOKE" "RIGHT" "ROLE" "ROLLBACK" "ROLLUP"
          "ROUTINE" "ROWS" "SAVEPOINT" "SCHEMA" "SCROLL" "SEARCH" "SECOND"
          "SECTION" "SELECT" "SEQUENCE" "SESSION" "SET" "SETS" "SIZE" "SOME"
          "SPACE" "SPECIFIC" "SPECIFICTYPE" "SQL" "SQLEXCEPTION" "SQLSTATE"
          "SQLWARNING" "START" "STATE" "STATEMENT" "STATIC" "STRUCTURE" "TABLE"
          "TEMPORARY" "TERMINATE" "THAN" "THEN" "TIMEZONE_HOUR"
          "TIMEZONE_MINUTE" "TO" "TRAILING" "TRANSACTION" "TRANSLATION"
          "TRIGGER" "TRUE" "UNDER" "UNION" "UNIQUE" "UNKNOWN" "UNNEST" "UPDATE"
          "USAGE" "USING" "VALUE" "VALUES" "VARIABLE" "VIEW" "WHEN" "WHENEVER"
          "WHERE" "WITH" "WITHOUT" "WORK" "WRITE" "YEAR"))
   (cons "Functions"
         (list
          "abs" "avg" "bit_length" "cardinality" "cast" "char_length"
          "character_length" "coalesce" "convert" "count" "current_date"
          "current_path" "current_role" "current_time" "current_timestamp"
          "current_user" "extract" "localtime" "localtimestamp" "lower" "max"
          "min" "mod" "nullif" "octet_length" "overlay" "placing" "session_user"
          "substring" "sum" "system_user" "translate" "treat" "trim" "upper"
          "user"))))

(defun edbi:dbd-limit-format-fill (dbd table-name limit-num)
  "[internal] Fill the format and return a SQL string."
  (replace-regexp-in-string 
   "%limit%" (format "%s" limit-num)
   (replace-regexp-in-string
    "%table%" table-name (edbi:dbd-limit-format dbd))))

(defun edbi:dbd-init ()
  "[internal] Initialize `edbi:dbd' objects."
  (setq edbi:dbd-default
        (make-edbi:dbd :name "dbi:SQLite"
                       :table-info-args 
                       (lambda (conn) (list nil nil nil nil))
                       :table-info-filter
                       'edbi:dbd-default-table-info-filter
                       :column-info-args
                       (lambda (conn table) (list nil nil table nil))
                       :column-info-filter
                       'edbi:dbd-default-column-info-filter
                       :type-info-filter
                       'edbi:dbd-default-type-info-filter
                       :limit-format
                       "SELECT * FROM %table% LIMIT %limit%"
                       :keywords
                       'edbi:dbd-default-keywords))
  (loop for i in (list edbi:dbd-default
                       (edbi:dbd-init-postgresql)
                       (edbi:dbd-init-mysql)
                       (edbi:dbd-init-oracle))
        do
        (edbi:dbd-register i)))

(defun edbi:dbd-init-postgresql ()
  "[internal] Initialize `edbi:dbd' object for Postgresql."
        (make-edbi:dbd :name "dbi:SQLite"
                       :table-info-args 
                       (lambda (conn) (list nil nil nil nil))
                       :table-info-filter
                       'edbi:dbd-default-table-info-filter
                       :column-info-args
                       (lambda (conn table) (list nil nil table nil))
                       :column-info-filter
                       'edbi:dbd-default-column-info-filter
                       :type-info-filter
                       'edbi:dbd-default-type-info-filter
                       :limit-format
                       "SELECT * FROM %table% LIMIT %limit%"
                       :keywords
                       'edbi:dbd-init-postgresql-keywords))

(defun edbi:dbd-init-postgresql-keywords ()
  "[internal] "
  (list
   (cons "Function"
         (list
          "abbrev" "abs" "acos" "age" "area" "ascii" "asin" "atab2" "atan"
          "atan2" "avg" "bit_length" "both" "broadcast" "btrim" "cbrt" "ceil"
          "center" "char_length" "chr" "coalesce" "col_description" "convert"
          "cos" "cot" "count" "current_database" "current_date" "current_schema"
          "current_schemas" "current_setting" "current_time" "current_timestamp"
          "current_user" "currval" "date_part" "date_trunc" "decode" "degrees"
          "diameter" "encode" "exp" "extract" "floor" "get_bit" "get_byte"
          "has_database_privilege" "has_function_privilege"
          "has_language_privilege" "has_schema_privilege" "has_table_privilege"
          "height" "host" "initcap" "isclosed" "isfinite" "isopen" "leading"
          "length" "ln" "localtime" "localtimestamp" "log" "lower" "lpad"
          "ltrim" "masklen" "max" "min" "mod" "netmask" "network" "nextval"
          "now" "npoints" "nullif" "obj_description" "octet_length" "overlay"
          "pclose" "pg_client_encoding" "pg_function_is_visible"
          "pg_get_constraintdef" "pg_get_indexdef" "pg_get_ruledef"
          "pg_get_userbyid" "pg_get_viewdef" "pg_opclass_is_visible"
          "pg_operator_is_visible" "pg_table_is_visible" "pg_type_is_visible"
          "pi" "popen" "position" "pow" "quote_ident" "quote_literal" "radians"
          "radius" "random" "repeat" "replace" "round" "rpad" "rtrim"
          "session_user" "set_bit" "set_byte" "set_config" "set_masklen"
          "setval" "sign" "sin" "split_part" "sqrt" "stddev" "strpos" "substr"
          "substring" "sum" "tan" "timeofday" "to_ascii" "to_char" "to_date"
          "to_hex" "to_number" "to_timestamp" "trailing" "translate" "trim"
          "trunc" "upper" "variance" "version" "width"))
   (cons "Keyword"
         (list
          "ABORT" "ACCESS" "ADD" "AFTER" "AGGREGATE" "ALIGNMENT" "ALL" "ALTER"
          "ANALYZE" "AND" "ANY" "AS" "ASC" "ASSIGNMENT" "AUTHORIZATION"
          "BACKWARD" "BASETYPE" "BEFORE" "BEGIN" "BETWEEN" "BINARY" "BY" "CACHE"
          "CALLED" "CASCADE" "CASE" "CAST" "CHARACTERISTICS" "CHECK"
          "CHECKPOINT" "CLASS" "CLOSE" "CLUSTER" "COLUMN" "COMMENT" "COMMIT"
          "COMMITTED" "COMMUTATOR" "CONSTRAINT" "CONSTRAINTS" "CONVERSION"
          "COPY" "CREATE" "CREATEDB" "CREATEUSER" "CURSOR" "CYCLE" "DATABASE"
          "DEALLOCATE" "DECLARE" "DEFAULT" "DEFERRABLE" "DEFERRED" "DEFINER"
          "DELETE" "DELIMITER" "DESC" "DISTINCT" "DO" "DOMAIN" "DROP" "EACH"
          "ELEMENT" "ELSE" "ENCODING" "ENCRYPTED" "END" "ESCAPE" "EXCEPT"
          "EXCLUSIVE" "EXECUTE" "EXISTS" "EXPLAIN" "EXTENDED" "EXTERNAL" "FALSE"
          "FETCH" "FINALFUNC" "FOR" "FORCE" "FOREIGN" "FORWARD" "FREEZE" "FROM"
          "FULL" "FUNCTION" "GRANT" "GROUP" "GTCMP" "HANDLER" "HASHES" "HAVING"
          "IMMEDIATE" "IMMUTABLE" "IMPLICIT" "IN" "INCREMENT" "INDEX" "INHERITS"
          "INITCOND" "INITIALLY" "INPUT" "INSENSITIVE" "INSERT" "INSTEAD"
          "INTERNALLENGTH" "INTERSECT" "INTO" "INVOKER" "IS" "ISNULL"
          "ISOLATION" "JOIN" "KEY" "LANGUAGE" "LEFTARG" "LEVEL" "LIKE" "LIMIT"
          "LISTEN" "LOAD" "LOCAL" "LOCATION" "LOCK" "LTCMP" "MAIN" "MATCH"
          "MAXVALUE" "MERGES" "MINVALUE" "MODE" "MOVE" "NATURAL" "NEGATOR"
          "NEXT" "NOCREATEDB" "NOCREATEUSER" "NONE" "NOT" "NOTHING" "NOTIFY"
          "NOTNULL" "NULL" "OF" "OFFSET" "OIDS" "ON" "ONLY" "OPERATOR" "OR"
          "ORDER" "OUTPUT" "OWNER" "PARTIAL" "PASSEDBYVALUE" "PASSWORD" "PLAIN"
          "PREPARE" "PRIMARY" "PRIOR" "PRIVILEGES" "PROCEDURAL" "PROCEDURE"
          "PUBLIC" "READ" "RECHECK" "REFERENCES" "REINDEX" "RELATIVE" "RENAME"
          "RESET" "RESTRICT" "RETURNS" "REVOKE" "RIGHTARG" "ROLLBACK" "ROW"
          "RULE" "SCHEMA" "SCROLL" "SECURITY" "SELECT" "SEQUENCE" "SERIALIZABLE"
          "SESSION" "SET" "SFUNC" "SHARE" "SHOW" "SIMILAR" "SOME" "SORT1"
          "SORT2" "STABLE" "START" "STATEMENT" "STATISTICS" "STORAGE" "STRICT"
          "STYPE" "SYSID" "TABLE" "TEMP" "TEMPLATE" "TEMPORARY" "THEN" "TO"
          "TRANSACTION" "TRIGGER" "TRUE" "TRUNCATE" "TRUSTED" "TYPE"
          "UNENCRYPTED" "UNION" "UNIQUE" "UNKNOWN" "UNLISTEN" "UNTIL" "UPDATE"
          "USAGE" "USER" "USING" "VACUUM" "VALID" "VALIDATOR" "VALUES"
          "VARIABLE" "VERBOSE" "VIEW" "VOLATILE" "WHEN" "WHERE" "WITH" "WITHOUT"
          "WORK"))))

(defun edbi:dbd-init-mysql ()
  "[internal] Initialize `edbi:dbd' object for MySQL."
  (make-edbi:dbd :name "dbi:mysql"
                 :table-info-args 
                 (lambda (conn) (list nil nil nil nil))
                 :table-info-filter
                 'edbi:dbd-default-table-info-filter
                 :column-info-args
                 (lambda (conn table) (list nil nil table "%"))
                 :column-info-filter
                 'edbi:dbd-default-column-info-filter
                 :type-info-filter
                 'edbi:dbd-default-type-info-filter
                 :limit-format
                 "SELECT * FROM %table% LIMIT %limit%"
                 :keywords
                 'edbi:dbd-init-mysql-keywords))

(defun edbi:dbd-init-mysql-keywords ()
  "[internal] "
  (list
   (cons "Function"
         (list
          "ascii" "avg" "bdmpolyfromtext" "bdmpolyfromwkb" "bdpolyfromtext"
          "bdpolyfromwkb" "benchmark" "bin" "bit_and" "bit_length" "bit_or"
          "bit_xor" "both" "cast" "char_length" "character_length" "coalesce"
          "concat" "concat_ws" "connection_id" "conv" "convert" "count"
          "curdate" "current_date" "current_time" "current_timestamp" "curtime"
          "elt" "encrypt" "export_set" "field" "find_in_set" "found_rows" "from"
          "geomcollfromtext" "geomcollfromwkb" "geometrycollectionfromtext"
          "geometrycollectionfromwkb" "geometryfromtext" "geometryfromwkb"
          "geomfromtext" "geomfromwkb" "get_lock" "group_concat" "hex" "ifnull"
          "instr" "interval" "isnull" "last_insert_id" "lcase" "leading"
          "length" "linefromtext" "linefromwkb" "linestringfromtext"
          "linestringfromwkb" "load_file" "locate" "lower" "lpad" "ltrim"
          "make_set" "master_pos_wait" "max" "mid" "min" "mlinefromtext"
          "mlinefromwkb" "mpointfromtext" "mpointfromwkb" "mpolyfromtext"
          "mpolyfromwkb" "multilinestringfromtext" "multilinestringfromwkb"
          "multipointfromtext" "multipointfromwkb" "multipolygonfromtext"
          "multipolygonfromwkb" "now" "nullif" "oct" "octet_length" "ord"
          "pointfromtext" "pointfromwkb" "polyfromtext" "polyfromwkb"
          "polygonfromtext" "polygonfromwkb" "position" "quote" "rand"
          "release_lock" "repeat" "replace" "reverse" "rpad" "rtrim" "soundex"
          "space" "std" "stddev" "substring" "substring_index" "sum" "sysdate"
          "trailing" "trim" "ucase" "unix_timestamp" "upper" "user" "variance"))
   (cons "Keyword"
         (list
          "ACTION" "ADD" "AFTER" "AGAINST" "ALL" "ALTER" "AND" "AS" "ASC"
          "AUTO_INCREMENT" "AVG_ROW_LENGTH" "BDB" "BETWEEN" "BY" "CASCADE"
          "CASE" "CHANGE" "CHARACTER" "CHECK" "CHECKSUM" "CLOSE" "COLLATE"
          "COLLATION" "COLUMN" "COLUMNS" "COMMENT" "COMMITTED" "CONCURRENT"
          "CONSTRAINT" "CREATE" "CROSS" "DATA" "DATABASE" "DEFAULT"
          "DELAY_KEY_WRITE" "DELAYED" "DELETE" "DESC" "DIRECTORY" "DISABLE"
          "DISTINCT" "DISTINCTROW" "DO" "DROP" "DUMPFILE" "DUPLICATE" "ELSE"
          "ENABLE" "ENCLOSED" "END" "ESCAPED" "EXISTS" "FIELDS" "FIRST" "FOR"
          "FORCE" "FOREIGN" "FROM" "FULL" "FULLTEXT" "GLOBAL" "GROUP" "HANDLER"
          "HAVING" "HEAP" "HIGH_PRIORITY" "IF" "IGNORE" "IN" "INDEX" "INFILE"
          "INNER" "INSERT" "INSERT_METHOD" "INTO" "IS" "ISAM" "ISOLATION" "JOIN"
          "KEY" "KEYS" "LAST" "LEFT" "LEVEL" "LIKE" "LIMIT" "LINES" "LOAD"
          "LOCAL" "LOCK" "LOW_PRIORITY" "MATCH" "MAX_ROWS" "MERGE" "MIN_ROWS"
          "MODE" "MODIFY" "MRG_MYISAM" "MYISAM" "NATURAL" "NEXT" "NO" "NOT"
          "NULL" "OFFSET" "OJ" "ON" "OPEN" "OPTIONALLY" "OR" "ORDER" "OUTER"
          "OUTFILE" "PACK_KEYS" "PARTIAL" "PASSWORD" "PREV" "PRIMARY"
          "PROCEDURE" "QUICK" "RAID0" "RAID_TYPE" "READ" "REFERENCES" "RENAME"
          "REPEATABLE" "RESTRICT" "RIGHT" "ROLLBACK" "ROLLUP" "ROW_FORMAT"
          "SAVEPOINT" "SELECT" "SEPARATOR" "SERIALIZABLE" "SESSION" "SET"
          "SHARE" "SHOW" "SQL_BIG_RESULT" "SQL_BUFFER_RESULT" "SQL_CACHE"
          "SQL_CALC_FOUND_ROWS" "SQL_NO_CACHE" "SQL_SMALL_RESULT" "STARTING"
          "STRAIGHT_JOIN" "STRIPED" "TABLE" "TABLES" "TEMPORARY" "TERMINATED"
          "THEN" "TO" "TRANSACTION" "TRUNCATE" "TYPE" "UNCOMMITTED" "UNION"
          "UNIQUE" "UNLOCK" "UPDATE" "USE" "USING" "VALUES" "WHEN" "WHERE"
          "WITH" "WRITE" "XOR"))))

(defun edbi:dbd-init-mssql ()
  "[internal] Initialize `edbi:dbd' object for MS SQLServer (Sybase DBD)."
  ;; TODO
  ;; define edbi:dbd and register 
  ;; also define?  ADO.NET, ODBC
  )

(defun edbi:dbd-init-oracle ()
  "[internal] Initialize `edbi:dbd' object for Oracle."
  (make-edbi:dbd :name "dbi:Oracle"
                 :table-info-args 
                 (lambda (conn) (list nil nil nil nil))
                 :table-info-filter
                 'edbi:dbd-oracle-table-info-filter
                 :column-info-args
                 (lambda (conn table) (list nil nil table "%"))
                 :column-info-filter
                 'edbi:dbd-default-column-info-filter
                 :type-info-filter
                 'edbi:dbd-default-type-info-filter
                 :limit-format
                 "SELECT * FROM (SELECT * FROM %table%) WHERE ROWNUM <= %limit%"
                 :keywords
                 'edbi:dbd-init-oracle-keywords))

(defun edbi:dbd-oracle-table-info-filter (table-info)
  "[internal] Default table name filter."
  (loop for rec in (edbi:dbd-extract-table-info table-info)
        for (catalog schema table type remarks) = rec
        if (and (string-match "^\\(TABLE\\|VIEW\\)$" type)
                (not (string-match "^\\(.*SYS\\|SYSTEM\\|PUBLIC\\|APEX_.+\\|XDB\\|ORDDATA\\)$" schema)))
        collect rec))

(defun edbi:dbd-init-oracle-keywords ()
  "[internal] "
  (list
   (cons "Function"
         (list
          "abs" "acos" "add_months" "ascii" "asciistr" "asin" "atan" "atan2"
          "avg" "bfilename" "bin_to_num" "bitand" "cast" "ceil" "chartorowid"
          "chr" "coalesce" "compose" "concat" "convert" "corr" "cos" "cosh"
          "count" "covar_pop" "covar_samp" "cume_dist" "current_date"
          "current_timestamp" "current_user" "dbtimezone" "decode" "decompose"
          "dense_rank" "depth" "deref" "dump" "empty_clob" "existsnode" "exp"
          "extract" "extractvalue" "first" "first_value" "floor" "following"
          "from_tz" "greatest" "group_id" "grouping_id" "hextoraw" "initcap"
          "instr" "lag" "last" "last_day" "last_value" "lead" "least" "length"
          "ln" "localtimestamp" "lower" "lpad" "ltrim" "make_ref" "max" "min"
          "mod" "months_between" "new_time" "next_day" "nls_charset_decl_len"
          "nls_charset_id" "nls_charset_name" "nls_initcap" "nls_lower"
          "nls_upper" "nlssort" "ntile" "nullif" "numtodsinterval"
          "numtoyminterval" "nvl" "nvl2" "over" "path" "percent_rank"
          "percentile_cont" "percentile_disc" "power" "preceding" "rank"
          "ratio_to_report" "rawtohex" "rawtonhex" "reftohex" "regr_"
          "regr_avgx" "regr_avgy" "regr_count" "regr_intercept" "regr_r2"
          "regr_slope" "regr_sxx" "regr_sxy" "regr_syy" "replace" "round"
          "row_number" "rowidtochar" "rowidtonchar" "rpad" "rtrim"
          "sessiontimezone" "sign" "sin" "sinh" "soundex" "sqrt" "stddev"
          "stddev_pop" "stddev_samp" "substr" "sum" "sys_connect_by_path"
          "sys_context" "sys_dburigen" "sys_extract_utc" "sys_guid" "sys_typeid"
          "sys_xmlagg" "sys_xmlgen" "sysdate" "systimestamp" "tan" "tanh"
          "to_char" "to_clob" "to_date" "to_dsinterval" "to_lob" "to_multi_byte"
          "to_nchar" "to_nclob" "to_number" "to_single_byte" "to_timestamp"
          "to_timestamp_tz" "to_yminterval" "translate" "treat" "trim" "trunc"
          "tz_offset" "uid" "unbounded" "unistr" "updatexml" "upper" "user"
          "userenv" "var_pop" "var_samp" "variance" "vsize" "width_bucket" "xml"
          "xmlagg" "xmlattribute" "xmlcolattval" "xmlconcat" "xmlelement"
          "xmlforest" "xmlsequence" "xmltransform"
          ))
   (cons "Keyword"
         (list
          "ABORT" "ACCESS" "ACCESSED" "ACCOUNT" "ACTIVATE" "ADD" "ADMIN"
          "ADVISE" "AFTER" "AGENT" "AGGREGATE" "ALL" "ALLOCATE" "ALLOW" "ALTER"
          "ALWAYS" "ANALYZE" "ANCILLARY" "AND" "ANY" "APPLY" "ARCHIVE"
          "ARCHIVELOG" "ARRAY" "AS" "ASC" "ASSOCIATE" "AT" "ATTRIBUTE"
          "ATTRIBUTES" "AUDIT" "AUTHENTICATED" "AUTHID" "AUTHORIZATION" "AUTO"
          "AUTOALLOCATE" "AUTOMATIC" "AVAILABILITY" "BACKUP" "BEFORE" "BEGIN"
          "BEHALF" "BETWEEN" "BINDING" "BITMAP" "BLOCK" "BLOCKSIZE" "BODY"
          "BOTH" "BUFFER_POOL" "BUILD" "BY"  "CACHE" "CALL" "CANCEL"
          "CASCADE" "CASE" "CATEGORY" "CERTIFICATE" "CHAINED" "CHANGE" "CHECK"
          "CHECKPOINT" "CHILD" "CHUNK" "CLASS" "CLEAR" "CLONE" "CLOSE" "CLUSTER"
          "COLUMN" "COLUMN_VALUE" "COLUMNS" "COMMENT" "COMMIT" "COMMITTED"
          "COMPATIBILITY" "COMPILE" "COMPLETE" "COMPOSITE_LIMIT" "COMPRESS"
          "COMPUTE" "CONNECT" "CONNECT_TIME" "CONSIDER" "CONSISTENT"
          "CONSTRAINT" "CONSTRAINTS" "CONSTRUCTOR" "CONTENTS" "CONTEXT"
          "CONTINUE" "CONTROLFILE" "CORRUPTION" "COST" "CPU_PER_CALL"
          "CPU_PER_SESSION" "CREATE" "CROSS" "CUBE" "CURRENT" "CURRVAL" "CYCLE"
          "DANGLING" "DATA" "DATABASE" "DATAFILE" "DATAFILES" "DAY" "DDL"
          "DEALLOCATE" "DEBUG" "DEFAULT" "DEFERRABLE" "DEFERRED" "DEFINER"
          "DELAY" "DELETE" "DEMAND" "DESC" "DETERMINES" "DETERMINISTIC"
          "DICTIONARY" "DIMENSION" "DIRECTORY" "DISABLE" "DISASSOCIATE"
          "DISCONNECT" "DISTINCT" "DISTINGUISHED" "DISTRIBUTED" "DML" "DROP"
          "EACH" "ELEMENT" "ELSE" "ENABLE" "END" "EQUALS_PATH" "ESCAPE"
          "ESTIMATE" "EXCEPT" "EXCEPTIONS" "EXCHANGE" "EXCLUDING" "EXISTS"
          "EXPIRE" "EXPLAIN" "EXTENT" "EXTERNAL" "EXTERNALLY"
          "FAILED_LOGIN_ATTEMPTS" "FAST" "FILE" "FINAL" "FINISH" "FLUSH" "FOR"
          "FORCE" "FOREIGN" "FREELIST" "FREELISTS" "FREEPOOLS" "FRESH" "FROM"
          "FULL" "FUNCTION" "FUNCTIONS" "GENERATED" "GLOBAL" "GLOBAL_NAME"
          "GLOBALLY" "GRANT" "GROUP" "GROUPING" "GROUPS" "GUARD" "HASH"
          "HASHKEYS" "HAVING" "HEAP" "HIERARCHY" "ID" "IDENTIFIED" "IDENTIFIER"
          "IDLE_TIME" "IMMEDIATE" "IN" "INCLUDING" "INCREMENT" "INDEX" "INDEXED"
          "INDEXES" "INDEXTYPE" "INDEXTYPES" "INDICATOR" "INITIAL" "INITIALIZED"
          "INITIALLY" "INITRANS" "INNER" "INSERT" "INSTANCE" "INSTANTIABLE"
          "INSTEAD" "INTERSECT" "INTO" "INVALIDATE" "IS" "ISOLATION" "JAVA"
          "JOIN"  "KEEP" "KEY" "KILL" "LANGUAGE" "LEFT" "LESS" "LEVEL"
          "LEVELS" "LIBRARY" "LIKE" "LIKE2" "LIKE4" "LIKEC" "LIMIT" "LINK"
          "LIST" "LOB" "LOCAL" "LOCATION" "LOCATOR" "LOCK" "LOG" "LOGFILE"
          "LOGGING" "LOGICAL" "LOGICAL_READS_PER_CALL"
          "LOGICAL_READS_PER_SESSION"  "MANAGED" "MANAGEMENT" "MANUAL" "MAP"
          "MAPPING" "MASTER" "MATCHED" "MATERIALIZED" "MAXDATAFILES"
          "MAXEXTENTS" "MAXIMIZE" "MAXINSTANCES" "MAXLOGFILES" "MAXLOGHISTORY"
          "MAXLOGMEMBERS" "MAXSIZE" "MAXTRANS" "MAXVALUE" "MEMBER" "MEMORY"
          "MERGE" "MIGRATE" "MINEXTENTS" "MINIMIZE" "MINIMUM" "MINUS" "MINVALUE"
          "MODE" "MODIFY" "MONITORING" "MONTH" "MOUNT" "MOVE" "MOVEMENT" "NAME"
          "NAMED" "NATURAL" "NESTED" "NEVER" "NEW" "NEXT" "NEXTVAL" "NO"
          "NOARCHIVELOG" "NOAUDIT" "NOCACHE" "NOCOMPRESS" "NOCOPY" "NOCYCLE"
          "NODELAY" "NOFORCE" "NOLOGGING" "NOMAPPING" "NOMAXVALUE" "NOMINIMIZE"
          "NOMINVALUE" "NOMONITORING" "NONE" "NOORDER" "NOPARALLEL" "NORELY"
          "NORESETLOGS" "NOREVERSE" "NORMAL" "NOROWDEPENDENCIES" "NOSORT"
          "NOSWITCH" "NOT" "NOTHING" "NOTIMEOUT" "NOVALIDATE" "NOWAIT" "NULL"
          "NULLS" "OBJECT" "OF" "OFF" "OFFLINE" "OIDINDEX" "OLD" "ON" "ONLINE"
          "ONLY" "OPEN" "OPERATOR" "OPTIMAL" "OPTION" "OR" "ORDER"
          "ORGANIZATION" "OUT" "OUTER" "OUTLINE" "OVERFLOW" "OVERRIDING"
          "PACKAGE" "PACKAGES" "PARALLEL" "PARALLEL_ENABLE" "PARAMETERS"
          "PARENT" "PARTITION" "PARTITIONS" "PASSWORD" "PASSWORD_GRACE_TIME"
          "PASSWORD_LIFE_TIME" "PASSWORD_LOCK_TIME" "PASSWORD_REUSE_MAX"
          "PASSWORD_REUSE_TIME" "PASSWORD_VERIFY_FUNCTION" "PCTFREE"
          "PCTINCREASE" "PCTTHRESHOLD" "PCTUSED" "PCTVERSION" "PERCENT"
          "PERFORMANCE" "PERMANENT" "PFILE" "PHYSICAL" "PIPELINED" "PLAN"
          "POST_TRANSACTION" "PRAGMA" "PREBUILT" "PRESERVE" "PRIMARY" "PRIVATE"
          "PRIVATE_SGA" "PRIVILEGES" "PROCEDURE" "PROFILE" "PROTECTION" "PUBLIC"
          "PURGE" "QUERY" "QUIESCE" "QUOTA" "RANGE" "READ" "READS" "REBUILD"
          "RECORDS_PER_BLOCK" "RECOVER" "RECOVERY" "RECYCLE" "REDUCED" "REF"
          "REFERENCES" "REFERENCING" "REFRESH" "REGISTER" "REJECT" "RELATIONAL"
          "RELY" "RENAME" "RESET" "RESETLOGS" "RESIZE" "RESOLVE" "RESOLVER"
          "RESOURCE" "RESTRICT" "RESTRICT_REFERENCES" "RESTRICTED" "RESULT"
          "RESUMABLE" "RESUME" "RETENTION" "RETURN" "RETURNING" "REUSE"
          "REVERSE" "REVOKE" "REWRITE" "RIGHT" "RNDS" "RNPS" "ROLE" "ROLES"
          "ROLLBACK" "ROLLUP" "ROW" "ROWDEPENDENCIES" "ROWNUM" "ROWS" "SAMPLE"
          "SAVEPOINT" "SCAN" "SCHEMA" "SCN" "SCOPE" "SEGMENT" "SELECT"
          "SELECTIVITY" "SELF" "SEQUENCE" "SERIALIZABLE" "SESSION"
          "SESSIONS_PER_USER" "SET" "SETS" "SETTINGS" "SHARED" "SHARED_POOL"
          "SHRINK" "SHUTDOWN" "SIBLINGS" "SID" "SINGLE" "SIZE" "SKIP" "SOME"
          "SORT" "SOURCE" "SPACE" "SPECIFICATION" "SPFILE" "SPLIT" "STANDBY"
          "START" "STATEMENT_ID" "STATIC" "STATISTICS" "STOP" "STORAGE" "STORE"
          "STRUCTURE" "SUBPARTITION" "SUBPARTITIONS" "SUBSTITUTABLE"
          "SUCCESSFUL" "SUPPLEMENTAL" "SUSPEND" "SWITCH" "SWITCHOVER" "SYNONYM"
          "SYS" "SYSTEM" "TABLE" "TABLES" "TABLESPACE" "TEMPFILE" "TEMPLATE"
          "TEMPORARY" "TEST" "THAN" "THEN" "THREAD" "THROUGH" "TIME_ZONE"
          "TIMEOUT" "TO" "TRACE" "TRANSACTION" "TRIGGER" "TRIGGERS" "TRUNCATE"
          "TRUST" "TYPE" "TYPES" "UNARCHIVED" "UNDER" "UNDER_PATH" "UNDO"
          "UNIFORM" "UNION" "UNIQUE" "UNLIMITED" "UNLOCK" "UNQUIESCE"
          "UNRECOVERABLE" "UNTIL" "UNUSABLE" "UNUSED" "UPDATE" "UPGRADE" "USAGE"
          "USE" "USING" "VALIDATE" "VALIDATION" "VALUE" "VALUES" "VARIABLE"
          "VARRAY" "VERSION" "VIEW" "WAIT" "WHEN" "WHENEVER" "WHERE" "WITH"
          "WITHOUT" "WNDS" "WNPS" "WORK" "WRITE" "XMLDATA" "XMLSCHEMA" "XMLTYPE"
          ))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Interface

(defface edbi:face-title
  '((((class color) (background light))
     :foreground "DarkGrey" :weight bold :height 1.2 :inherit variable-pitch)
    (((class color) (background dark))
     :foreground "darkgoldenrod3" :weight bold :height 1.2 :inherit variable-pitch)
    (t :height 1.2 :weight bold :inherit variable-pitch))
  "Face for title" :group 'edbi)

(defface edbi:face-header
  '((((class color) (background light))
     :foreground "Slategray4" :background "Gray90" :weight bold)
    (((class color) (background dark))
     :foreground "maroon2" :weight bold))
  "Face for headers" :group 'edbi)

(defface edbi:face-error
  '((((class color) (background light))
     :foreground "red" :weight bold)
    (((class color) (background dark))
     :foreground "red" :weight bold))
  "Face for error" :group 'edbi)


;; Data Source history

(defvar edbi:ds-history-file (expand-file-name ".edbi-ds-history" user-emacs-directory) "Data source history file.")
(defvar edbi:ds-history-list-num 10 "Maximum history number.")

(defvar edbi:ds-history-list nil "[internal] data source history.")

(defun edbi:ds-history-add (ds)
  "[internal] Add the given data source into `edbi:ds-history-list'. This function truncates the list, if the length of the list is more than `edbi:ds-history-list-num'."
  (let ((dsc (edbi:data-source
              (edbi:data-source-uri ds)
              (edbi:data-source-username ds) "")))
    (setq edbi:ds-history-list
          (remove-if (lambda (i) 
                       (equal (edbi:data-source-uri i)
                              (edbi:data-source-uri dsc))) 
                     edbi:ds-history-list))
    (push dsc edbi:ds-history-list)
    (setq edbi:ds-history-list
          (loop for i in edbi:ds-history-list
                for idx from 0 below (min (length edbi:ds-history-list)
                                          edbi:ds-history-list-num)
                collect i))
    (edbi:ds-history-save)))

(defun edbi:ds-history-save ()
  "[internal] Save the data source history `edbi:ds-history-list' into the file `edbi:ds-history-file'."
  (let* ((file (expand-file-name edbi:ds-history-file))
         (coding-system-for-write 'utf-8)
         after-save-hook before-save-hook
         (buf (find-file-noselect file)))
    (unwind-protect
        (with-current-buffer buf
          (set-visited-file-name nil)
          (buffer-disable-undo)
          (erase-buffer)
          (insert 
           (prin1-to-string edbi:ds-history-list))
          (write-region (point-min) (point-max) file nil 'ok))
      (kill-buffer buf)))
  nil)

(defun edbi:ds-history-load ()
  "[internal] Read the data source history file and store the data into `edbi:ds-history-list'."
  (let* ((coding-system-for-read 'utf-8)
         (file (expand-file-name edbi:ds-history-file)))
    (when (file-exists-p file)
      (let ((buf (find-file-noselect file)) ret)
        (unwind-protect
            (setq ret (loop for i in (read buf)
                            collect 
                            (edbi:data-source (car i) (nth 1 i) "")))
          (kill-buffer buf))
        (setq edbi:ds-history-list ret)))))


;; Data Source dialog

(defun edbi:get-new-buffer (buffer-name)
  "[internal] Create and return a buffer object.
This function kills the old buffer if it exists."
  (let ((buf (get-buffer buffer-name)))
    (when (and buf (buffer-live-p buf))
      (kill-buffer buf)))
  (get-buffer-create buffer-name))

(defvar edbi:dialog-buffer-name "*edbi-dialog-ds*" "[internal] edbi:dialog-buffer-name.")

(defun edbi:dialog-ds-buffer (data-source on-ok-func 
                                          &optional password-show error-msg)
  "[internal] Create and return the editing buffer for the given DATA-SOURCE."
  (let ((buf (edbi:get-new-buffer edbi:dialog-buffer-name)))
    (with-current-buffer buf
      (let ((inhibit-read-only t)) (erase-buffer))
      (kill-all-local-variables)
      (remove-overlays)
      (erase-buffer)
      (widget-insert (format "Data Source: [driver: %s]\n\n" edbi:driver-info))
      (when error-msg
        (widget-insert
         (let ((text (substring-no-properties error-msg)))
           (put-text-property 0 (length text) 'face 'font-lock-warning-face text)
           text))
        (widget-insert "\n\n"))
      (lexical-let 
          ((data-source data-source) (on-ok-func on-ok-func) (error-msg error-msg)
           fdata-source fusername fauth cbshow menu-history fields)
        ;; create dialog fields
        (setq fdata-source
              (widget-create
               'editable-field
               :size 30 :format "  Data Source: %v \n"
               :value (or (edbi:data-source-uri data-source) ""))
              fusername
              (widget-create
               'editable-field
               :size 20 :format "   User Name : %v \n"
               :value (or (edbi:data-source-username data-source) ""))
              fauth 
              (widget-create
               'editable-field
               :size 20 :format "        Auth : %v \n"
               :secret (and (not password-show) ?*)
               :value (or (edbi:data-source-auth data-source) "")))
        (widget-insert "    (show auth ")
        (setq cbshow
              (widget-create 'checkbox  :value password-show))
        (widget-insert " ) ")
        (setq fields
              (list 'data-source fdata-source
                    'username fusername 'auth fauth 
                    'password-show cbshow))

        ;; history
        (widget-insert "\n")
        (setq menu-history
              (widget-create 
               'menu-choice
               :format "    %[%t%] : %v"
               :tag "History"
               :help-echo "Click to choose a history."
               :value data-source
               :args
               (cons '(item :tag "(not selected)" :value (nil nil nil))
                     (loop for i in edbi:ds-history-list
                           collect
                           (list 'item ':tag
                                 (format "[%s]" (edbi:data-source-uri i))
                                 ':value i)))))

        ;; OK / Cancel
        (widget-insert "\n")
        (widget-create 
         'push-button
         :notify (lambda (&rest ignore)
                   (edbi:dialog-ds-commit data-source fields on-ok-func))
         "Ok")
        (widget-insert " ")
        (widget-create
         'push-button
         :notify (lambda (&rest ignore)
                   (edbi:dialog-ds-kill-buffer))
         "Cancel")
        (widget-insert "\n")

        ;; add event actions
        (widget-put cbshow
                    :notify
                    (lambda (&rest ignore)
                      (let ((current-ds
                             (edbi:data-source
                              (widget-value fdata-source)
                              (widget-value fusername)
                              (widget-value fauth)))
                            (password-show (widget-value cbshow)))
                        (edbi:dialog-replace-buffer-window
                         (current-buffer)
                         current-ds on-ok-func password-show error-msg)
                        (widget-forward 3))))
        (widget-put menu-history
                    :notify 
                    (lambda (widget &rest ignore)
                        (edbi:dialog-replace-buffer-window
                         (current-buffer)
                         (widget-value widget) on-ok-func (widget-value cbshow))
                        (widget-forward 4)))

        ;; setup widgets
        (use-local-map widget-keymap)
        (widget-setup)
        (goto-char (point-min))
        (widget-forward 1)))
    buf))

(defun edbi:dialog-ds-cbshow (data-source fields on-ok-func)
  "[internal] Click action for the checkbox of [show auth]."
  (let ((current-ds
         (edbi:data-source
          (widget-value (plist-get fields 'data-source))
          (widget-value (plist-get fields 'username))
          (widget-value (plist-get fields 'auth))))
        (password-show (widget-value (plist-get fields 'cbshow))))
    (edbi:dialog-replace-buffer-window
     (current-buffer) current-ds on-ok-func password-show)
    (widget-forward 3)))

(defun edbi:dialog-ds-commit (data-source fields on-ok-func)
  "[internal] Click action for the [OK] button."
  (let ((uri-value (widget-value (plist-get fields 'data-source))))
    (cond
     ((or (null uri-value)
          (string-equal "" uri-value))
      (edbi:dialog-replace-buffer-window
       (current-buffer)
       data-source on-ok-func
       (widget-value (plist-get fields 'password-show))
       "Should not be empty!"))
     (t
      (setq data-source
            (edbi:data-source
             uri-value
             (widget-value (plist-get fields 'username))
             (widget-value (plist-get fields 'auth))))
      (edbi:ds-history-add data-source)
      (let ((msg (funcall on-ok-func data-source)))
        (if msg 
            (edbi:dialog-replace-buffer-window
             (current-buffer)
             data-source on-ok-func
             (widget-value (plist-get fields 'password-show))
             (format "Connection Error : %s" msg))
          (edbi:dialog-ds-kill-buffer)))))))

(defun edbi:dialog-ds-kill-buffer ()
  "[internal] Kill dialog buffer."
  (interactive)
  (let ((cbuf (current-buffer))
        (win-num (length (window-list))))
    (when (and (not (one-window-p))
               (> win-num edbi:dialog-before-win-num))
      (delete-window))
    (kill-buffer cbuf)))

(defvar edbi:dialog-before-win-num 0  "[internal] ")

(defun edbi:dialog-replace-buffer-window (prev-buf data-source on-ok-func 
                                                   &optional password-show error-msg)
  "[internal] Kill the previous dialog buffer and create new dialog buffer."
  (let ((win (get-buffer-window prev-buf)) new-buf)
    (setq new-buf
          (edbi:dialog-ds-buffer
           data-source on-ok-func password-show error-msg))
    (cond
     ((or (null win) (not (window-live-p win)))
      (pop-to-buffer new-buf))
     (t
      (set-window-buffer win new-buf)
      (set-buffer new-buf)))
    new-buf))

(defun edbi:dialog-ds-open (on-ok-func)
  "[internal] Display a dialog for data source information."
  (setq edbi:dialog-before-win-num (length (window-list)))
  (edbi:ds-history-load)
  (pop-to-buffer
   (edbi:dialog-ds-buffer
    (edbi:data-source nil) on-ok-func)))


;; database viewer

(defun edbi:open-db-viewer ()
  "Open Database viewer buffer."
  (interactive)
  (let ((connection-func
         (lambda (ds)
           (let (conn msg)
             (setq msg
                   (condition-case err
                       (progn
                         (setq conn (edbi:start))
                         (edbi:connect conn data-source)
                         nil)
                     (error (format "%s" err))))
             (cond
              ((null msg)
               (deferred:call 'edbi:dbview-open conn) nil)
              (t msg))))))
    (edbi:dialog-ds-open connection-func)))

(defvar edbi:dbview-buffer-name "*edbi-dbviewer*" "[internal] Database buffer name.")
(defvar edbi:connection nil "[internal] Buffer local variable.")

(defvar edbi:dbview-keymap
  (epc:add-keymap
   ctbl:table-mode-map
   '(
     ("g"   . edbi:dbview-update-command)
     ("SPC" . edbi:dbview-show-tabledef-command)
     ("c"   . edbi:dbview-query-editor-command)
     ("C"   . edbi:dbview-query-editor-new-command)
     ("C-m" . edbi:dbview-show-table-data-command)
     ("q"   . edbi:dbview-quit-command)
     )) "Keymap for the DB Viewer buffer.")

(defun edbi:dbview-header (data-source &optional items)
  "[internal] "
  (concat
   (propertize (format "DB: %s\n" (edbi:data-source-uri data-source))
               'face 'edbi:face-title)
   (if items
       (propertize (format "[%s items]\n" (length items))
                   'face 'edbi:face-header))))

(defvar edbi:dbview-update-hook nil "This hook is called after rendering the dbview buffer. The hook function should have one argument: `edbi:connection'.")

(defun edbi:dbview-open (conn)
  "[internal] Start EPC conversation with the DB to open the DB Viewer buffer."
  (lexical-let ((db-buf (edbi:get-new-buffer edbi:dbview-buffer-name)))
    (with-current-buffer db-buf
      (let (buffer-read-only)
        (erase-buffer)
        (set (make-local-variable 'edbi:connection) conn)
        (insert (edbi:dbview-header (edbi:connection-ds conn))
                "\n[connecting...]")))
    (unless (eq (current-buffer) db-buf)
      (pop-to-buffer db-buf))
    (lexical-let ((conn conn) (dbd (edbi:dbd-get conn)) table-info)
      (deferred:error
        (edbi:seq
         (table-info <- (apply 'edbi:table-info-d conn
                               (funcall (edbi:dbd-table-info-args dbd) conn)))
         (lambda (x) 
           (edbi:dbview-create-buffer conn dbd table-info))
         (lambda (x) 
           (run-hook-with-args 'edbi:dbview-update-hook conn)))
        (lambda (err)
          (with-current-buffer db-buf
            (let (buffer-read-only)
              (insert "\n" "Connection Error : " 
                      (format "%S" err) "\n" "Check your setting..."))))))))

(defun edbi:dbview-create-buffer (conn dbd table-info)
  "[internal] Render the DB Viewer buffer with the table-info."
  (let* ((buf (get-buffer-create edbi:dbview-buffer-name))
         (data (loop for (catalog schema table type remarks) in 
                     (funcall (edbi:dbd-table-info-filter dbd) table-info)
                     collect
                     (list (concat catalog schema) table type (or remarks "")
                           (list catalog schema table)))) table-cp)
    (with-current-buffer buf
      (let (buffer-read-only)
        (erase-buffer)
        (insert (edbi:dbview-header (edbi:connection-ds conn) data))
        (setq table-cp 
              (ctbl:create-table-component-region
               :model
               (make-ctbl:model
                :column-model
                (list (make-ctbl:cmodel :title "Schema"    :align 'left)
                      (make-ctbl:cmodel :title "Table Name" :align 'left)
                      (make-ctbl:cmodel :title "Type"  :align 'center)
                      (make-ctbl:cmodel :title "Remarks"  :align 'left))
                :data data
                :sort-state '(1 2))
               :keymap edbi:dbview-keymap))
        (goto-char (point-min))
        (ctbl:cp-set-selected-cell table-cp '(0 . 0)))
      (setq buffer-read-only t)
      buf)))

(eval-when-compile ; introduce anaphoric variable `cp' and `table'.
  (defmacro edbi:dbview-with-cp (&rest body)
    `(let ((cp (ctbl:cp-get-component)))
       (when cp
         (ctbl:cp-set-selected-cell cp (ctbl:cursor-to-nearest-cell))
         (let ((table (car (last (ctbl:cp-get-selected-data-row cp)))))
           ,@body)))))

(defun edbi:dbview-quit-command ()
  (interactive)
  (let ((conn edbi:connection))
    (edbi:dbview-with-cp
     (when (and conn (y-or-n-p "Quit and disconnect DB ? "))
       (edbi:finish conn)
       (when (and (edbi:connection-buffers conn)
                  (y-or-n-p "Kill all query and result buffers ? "))
         ;; kill tabledef buffer
         (let ((table-buf (get-buffer edbi:dbview-table-buffer-name)))
           (when (and table-buf (buffer-live-p table-buf))
             (kill-buffer table-buf)))
         ;; kill editor and result buffers
         (ignore-errors
           (loop for b in (edbi:connection-buffers conn)
                 if (and b (buffer-live-p b))
                 do 
                 (let ((rbuf (buffer-local-value 'edbi:result-buffer b)))
                   (when (and rbuf (kill-buffer rbuf))))
                 (kill-buffer b))))
       ;; kill db view buffer
       (kill-buffer (current-buffer))))))

(defun edbi:dbview-update-command ()
  (interactive)
  (let ((conn edbi:connection))
    (when conn
      (edbi:dbview-open conn))))

(defun edbi:dbview-show-tabledef-command ()
  (interactive)
  (let ((conn edbi:connection))
    (when conn
      (edbi:dbview-with-cp
       (destructuring-bind (catalog schema table) table
         (edbi:dbview-tabledef-open conn catalog schema table))))))

(defun edbi:dbview-query-editor-command ()
  (interactive)
  (let ((conn edbi:connection))
    (when conn
      (edbi:dbview-with-cp
       (edbi:dbview-query-editor-open conn)))))

(defun edbi:dbview-query-editor-new-command ()
  (interactive)
  (let ((conn edbi:connection))
    (when conn
      (edbi:dbview-with-cp
       (edbi:dbview-query-editor-open conn :force-create-p t)))))

(defvar edbi:dbview-show-table-data-default-limit 50
  "Maximum row numbers for default table viewer SQL.")

(defun edbi:dbview-show-data-sql (conn table-name)
  (if edbi:dbview-show-table-data-default-limit
      (edbi:dbd-limit-format-fill
       (edbi:dbd-get conn) table-name
       edbi:dbview-show-table-data-default-limit)
    (format "SELECT * FROM %s" table-name)))

(defun edbi:dbview-show-table-data-command ()
  (interactive)
  (let ((conn edbi:connection))
    (when conn
      (edbi:dbview-with-cp
       (destructuring-bind (catalog schema table-name) table
         (edbi:dbview-query-editor-open 
          conn 
          :init-sql (edbi:dbview-show-data-sql conn table-name)
          :executep t))))))


;; query editor and viewer

(defvar edbi:sql-mode-map 
  (epc:define-keymap
   '(
     ("C-c C-c" . edbi:dbview-query-editor-execute-command)
     ("C-c q"   . edbi:dbview-query-editor-quit-command)
     ("M-p"     . edbi:dbview-query-editor-history-back-command)
     ("M-n"     . edbi:dbview-query-editor-history-forward-command)
     ("C-c C-k" . edbi:dbview-query-editor-clear-buffer-command)
     )) "Keymap for the `edbi:sql-mode'.")

(defvar edbi:sql-mode-hook nil  "edbi:sql-mode-hook.")
(defvar edbi:result-buffer nil  "[internal] Buffer local variable.")

(defun edbi:sql-mode ()
  "Major mode for SQL. This function is copied from sql.el and modified."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'edbi:sql-mode)
  (setq mode-name "EDBI SQL")
  (use-local-map edbi:sql-mode-map)
  (set-syntax-table sql-mode-syntax-table)
  (make-local-variable 'font-lock-defaults)
  (make-local-variable 'sql-mode-font-lock-keywords)
  (make-local-variable 'comment-start)
  (setq comment-start "--")
  (make-local-variable 'paragraph-separate)
  (make-local-variable 'paragraph-start)
  (setq paragraph-separate "[\f]*$"     paragraph-start "[\n\f]")
  ;; Abbrevs
  (setq local-abbrev-table sql-mode-abbrev-table)
  (setq abbrev-all-caps 1)
  ;; Run hook
  (sql-product-font-lock nil t))

(defun edbi:dbview-query-editor-quit-command ()
  (interactive)
  (when (and edbi:result-buffer
             (buffer-live-p edbi:result-buffer)
             (y-or-n-p "Do you also kill the result buffer?"))
    (kill-buffer edbi:result-buffer))
  (kill-buffer))


(defvar edbi:dbview-uid 0 "[internal] ")

(defun edbi:dbview-uid ()
  "[internal] UID counter."
  (incf edbi:dbview-uid))


(defvar edbi:query-editor-history-max-num 50 "[internal] Maximum number of the query histories.")
(defvar edbi:query-editor-history-list nil "[internal] A list of the query histories.")
(defvar edbi:history-index   nil "[internal] A buffer local variable.")
(defvar edbi:history-current nil "[internal] A buffer local variable.")

(defun edbi:dbview-query-editor-history-back-command ()
  (interactive)
  (when (and edbi:history-index edbi:query-editor-history-list
             (< edbi:history-index (length edbi:query-editor-history-list)))
    (when (= 0 edbi:history-index)
      (setq edbi:history-current (buffer-string)))
    (erase-buffer)
    (setq edbi:history-index (1+ edbi:history-index))
    (insert (nth edbi:history-index edbi:query-editor-history-list))
    (message "Query history : [%s/%s]" 
             edbi:history-index
             (length edbi:query-editor-history-list))))

(defun edbi:dbview-query-editor-history-forward-command ()
  (interactive)
  (when (and edbi:history-index edbi:query-editor-history-list
             (> edbi:history-index 0))
    (setq edbi:history-index (1- edbi:history-index))
    (erase-buffer)
    (insert 
     (cond
      ((= 0 edbi:history-index) edbi:history-current)
      (t (nth edbi:history-index edbi:query-editor-history-list))))
    (message "Query history : [%s/%s]" 
             edbi:history-index
             (length edbi:query-editor-history-list))))

(defun edbi:dbview-query-editor-history-add (sql)
  "[internal] Add current SQL into history. This function assumes
that the current buffer is the query editor buffer."
  (push sql edbi:query-editor-history-list)
  (setq edbi:query-editor-history-list
        (loop for i in edbi:query-editor-history-list
              for idx from 0 below edbi:query-editor-history-max-num
              collect i)))

(defun edbi:dbview-query-editor-history-reset-index ()
  "[internal] Reset the history counter `edbi:history-index'."
  (setq edbi:history-index 0))

(defun edbi:dbview-query-editor-clear-buffer-command ()
  (interactive)
  (erase-buffer))

(defun edbi:dbview-query-editor-create-buffer (conn &optional force-create-p)
  "[internal] Create a buffer for query editor."
  (let ((buf-list (edbi:connection-buffers conn)))
    (cond
     ((and (car buf-list) (null force-create-p))
      (car buf-list))
     (t
      (let* ((uid (edbi:dbview-uid))
             (buf-name (format "*edbi:query-editor %s *" uid))
             (buf (get-buffer-create buf-name)))
        (with-current-buffer buf
          (edbi:sql-mode)
          (set (make-local-variable 'edbi:buffer-id) uid)
          (set (make-local-variable 'edbi:history-index) 0)
          (set (make-local-variable 'edbi:history-current) nil))
        (edbi:connection-buffers-set conn (cons buf buf-list))
        buf)))))

(defun* edbi:dbview-query-editor-open (conn &key init-sql executep force-create-p)
  "[internal] Open a query-editor buffer and display the buffer by the switch-to-buffer.
INIT-SQL is a string which is inserted in the buffer.
If EXECUTEP is non-nil, the INIT-SQL is executed after the displaying the buffer.
If FORCE-CREATE-P is non-nil, this function creates a new buffer."
  (let ((buf (edbi:dbview-query-editor-create-buffer conn force-create-p)))
    (with-current-buffer buf
      (set (make-local-variable 'edbi:connection) conn)
      (set (make-local-variable 'edbi:result-buffer) nil)
      (setq mode-line-format
            `("-" mode-line-mule-info
              " Query Editor:"
              " " ,(edbi:data-source-uri (edbi:connection-ds conn))
              " " mode-line-position
              " " global-mode-string
              " " "-%-"))
      (when init-sql
        (erase-buffer)
        (insert init-sql))
      (if (fboundp 'run-mode-hooks)
          (run-mode-hooks 'edbi:sql-mode-hook)
        (run-hooks 'edbi:sql-mode-hook)))
    (switch-to-buffer buf)
    (when executep
      (with-current-buffer buf
        (edbi:dbview-query-editor-execute-command)))
    buf))

(defun edbi:dbview-query-result-get-buffer (editor-buf)
  "[internal] "
  (let* ((uid (buffer-local-value 'edbi:buffer-id editor-buf))
         (rbuf-name (format "*edbi:query-result %s" uid))
         (rbuf (get-buffer rbuf-name)))
    (unless rbuf
      (setq rbuf (get-buffer-create rbuf-name)))
    rbuf))

(defun edbi:dbview-query-result-modeline (data-source)
  "[internal] Set mode line format for the query result."
  (setq mode-line-format
        `("-" mode-line-mule-info
          " Query Result:"
          " " ,(edbi:data-source-uri data-source)
          " " mode-line-position
          " " global-mode-string
          " " "-%-")))

(defun edbi:dbview-query-editor-execute-command ()
  "Execute SQL and show result buffer.
If the region is active in the query buffer, the selected string is executed."
  (interactive) 
  (when edbi:connection
    (let ((sql
           (if (region-active-p)
               (buffer-substring-no-properties (region-beginning) (region-end))
             (buffer-substring-no-properties (point-min) (point-max))))
          (result-buf edbi:result-buffer))
      (edbi:dbview-query-editor-history-reset-index)
      (unless (and result-buf (buffer-live-p result-buf))
        (setq result-buf (edbi:dbview-query-result-get-buffer (current-buffer)))
        (setq edbi:result-buffer result-buf))
      (edbi:dbview-query-execute edbi:connection sql result-buf))))

(defvar edbi:dbview-query-execute-semaphore (cc:semaphore-create 1)
  "[internal] edbi:dbview-query-execute-semaphore.")

(defun edbi:dbview-query-execute-semaphore-clear ()
  (interactive)
  (cc:semaphore-release-all edbi:dbview-query-execute-semaphore))

(defun edbi:dbview-query-execute (conn sql result-buf)
  "[internal] "
  (lexical-let ((conn conn)
                (sql sql) (result-buf result-buf))
    (cc:semaphore-with edbi:dbview-query-execute-semaphore
      (lambda (x) 
        (deferred:$
          (edbi:seq
           (edbi:prepare-d conn sql)
           (edbi:execute-d conn nil)
           (lambda (exec-result)
             (message "Result Code: %S" exec-result) ; for debug
             (cond
              ;; SELECT
              ((or (equal "0E0" exec-result) 
                   (and exec-result (numberp exec-result))) ; some DBD returns rows number
               (edbi:dbview-query-editor-history-add sql)
               (lexical-let (rows header (exec-result exec-result))
                 (edbi:seq
                  (header <- (edbi:fetch-columns-d conn))
                  (rows <- (edbi:fetch-d conn))
                  (lambda (x)
                    (cond
                     ((or rows (equal "0E0" exec-result)) ; select results
                      (edbi:dbview-query-result-open conn result-buf header rows))
                     (t    ; update results?
                      (edbi:dbview-query-result-text conn result-buf exec-result)))))))
              ;; ERROR
              ((null exec-result)
               (edbi:dbview-query-result-error conn result-buf))
              ;; UPDATE etc
              (t 
               (edbi:dbview-query-editor-history-add sql)
               (edbi:dbview-query-result-text conn result-buf exec-result)))))
          (deferred:error it
            (lambda (err) (message "ERROR : %S" err))))))))

(defun edbi:dbview-query-result-text (conn buf execute-result)
  "[internal] Display update results."
  (with-current-buffer buf
    (let (buffer-read-only)
      (fundamental-mode)
      (edbi:dbview-query-result-modeline (edbi:connection-ds conn))
      (erase-buffer)
      (insert (format "OK. %s rows are affected.\n" execute-result)))
    (setq buffer-read-only t))
  (pop-to-buffer buf))

(defun edbi:dbview-query-result-error (conn buf)
  "[internal] Display errors."
  (let* ((status (edbi:sync edbi:status-info-d conn))
         (err-code (car status))
         (err-str (nth 1 status))
         (err-state (nth 2 status)))
    (with-current-buffer buf
      (let (buffer-read-only)
        (fundamental-mode)
        (edbi:dbview-query-result-modeline (edbi:connection-ds conn))
        (erase-buffer)
        (insert 
         (propertize
          (format "ERROR! [%s]" err-state)
          'face 'edbi:face-error)
         "\n" err-str))
      (setq buffer-read-only t))
    (pop-to-buffer buf)))

(defvar edbi:query-result-column-max-width 50 "Maximum column width for query results.")
(defvar edbi:query-result-fix-header t "Fixed header option for query results.")

(defvar edbi:dbview-query-result-keymap
  (epc:define-keymap
   '(
     ("q"   . edbi:dbview-query-result-quit-command)
     ("SPC" . edbi:dbview-query-result-quicklook-command)
     )) "Keymap for the query result viewer buffer.")

(defvar edbi:before-win-num nil "[internal] A buffer local variable.")

(defun edbi:dbview-query-result-open (conn buf header rows)
  "[internal] Display SELECT results."
  (let (table-cp (param (copy-ctbl:param ctbl:default-rendering-param)))
    (setf (ctbl:param-fixed-header param) edbi:query-result-fix-header)
    (setq table-cp
          (ctbl:create-table-component-buffer
           :buffer buf :param param
           :model
           (make-ctbl:model
            :column-model
            (loop for i in header
                  collect (make-ctbl:cmodel
                           :title (format "%s" i) :align 'left
                           :min-width 5 :max-width edbi:query-result-column-max-width))
            :data rows
            :sort-state nil)
           :custom-map edbi:dbview-query-result-keymap))
    (ctbl:cp-set-selected-cell table-cp '(0 . 0))
    (with-current-buffer buf
      (set (make-local-variable 'edbi:before-win-num) (length (window-list)))
      (edbi:dbview-query-result-modeline (edbi:connection-ds conn)))
    (pop-to-buffer buf)))

(defun edbi:dbview-query-result-quit-command ()
  "Quit the query result buffer."
  (interactive)
  (let ((cbuf (current-buffer))
        (win-num (length (window-list))))
    (when (and (not (one-window-p))
               (> win-num edbi:before-win-num))
      (delete-window))
    (kill-buffer cbuf)))

(defvar edbi:dbview-query-result-quicklook-buffer " *dbview-query-result-quicklook*" "[internal] ")

(defun edbi:dbview-query-result-quicklook-command ()
  "Display the cell content on the popup buffer."
  (interactive)
  (edbi:dbview-with-cp
   (let* ((cell-data (ctbl:cp-get-selected-data-cell cp))
          (buf (get-buffer-create edbi:dbview-query-result-quicklook-buffer)))
     (with-current-buffer buf
       (let (buffer-read-only)
         (edbi:dbview-query-result-quicklook-mode)
         (erase-buffer)
         (insert cell-data))
       (setq buffer-read-only t))
     (pop-to-buffer buf))))

(define-derived-mode edbi:dbview-query-result-quicklook-mode
  text-mode "Result Quicklook Mode"
  "Major mode for quicklooking the result data.
\\{edbi:dbview-query-result-quicklook-mode-map}"
  (setq case-fold-search nil))

(defun edbi:dbview-query-result-quicklook-copy-command ()
  "Copy the whole content."
  (interactive)
  (mark-whole-buffer)
  (copy-region-as-kill (point-min) (point-max)))

(setq edbi:dbview-query-result-quicklook-mode-map
      (epc:add-keymap
       edbi:dbview-query-result-quicklook-mode-map
       '(
         ("SPC" . kill-this-buffer)
         ("q"   . kill-this-buffer)
         ("C"   . edbi:dbview-query-result-quicklook-copy-command)
         )))


;; table definition viewer

(defvar edbi:dbview-table-buffer-name "*edbi-dbviewer-table*" "[internal] Table buffer name.")

(defvar edbi:dbview-table-keymap
  (epc:add-keymap
   ctbl:table-mode-map
   '(
     ("g"   . edbi:dbview-tabledef-update-command)
     ("q"   . edbi:dbview-tabledef-quit-command)
     ("c"   . edbi:dbview-tabledef-query-editor-command)
     ("C"   . edbi:dbview-tabledef-query-editor-new-command)
     ("V"   . edbi:dbview-tabledef-show-data-command)
     )) "Keymap for the DB Table Viewer buffer.")

(defvar edbi:tabledef nil "[internal] A buffer local variable.")

(defun edbi:dbview-tabledef-header (data-source table-name &optional items)
  "[internal] "
  (concat
   (propertize (format "Table: %s\n" table-name) 'face 'edbi:face-title)
   (format "DB: %s\n" (edbi:data-source-uri data-source))
   (if items
       (propertize (format "[%s items]\n" (length items)) 'face 'edbi:face-header))))

(defun edbi:dbview-tabledef-open (conn catalog schema table)
  "[internal] "
  (with-current-buffer
      (get-buffer-create edbi:dbview-table-buffer-name)
    (let (buffer-read-only)
      (erase-buffer)
      (set (make-local-variable 'edbi:before-win-num) (length (window-list)))
      (set (make-local-variable 'edbi:tabledef)
           (list conn catalog schema table))
      (insert (edbi:dbview-tabledef-header (edbi:connection-ds conn) table)
              "[connecting...]\n")))
  (unless (equal (buffer-name) edbi:dbview-table-buffer-name)
    (pop-to-buffer edbi:dbview-table-buffer-name))
  (lexical-let ((conn conn) 
                (catalog catalog) (schema schema) (table table)
                column-info pkey-info index-info)
    (edbi:seq
     (column-info <- (edbi:column-info-d conn catalog schema table nil))
     (pkey-info   <- (edbi:primary-key-info-d conn catalog schema table))
     (index-info  <- (edbi:table-info-d conn catalog schema table "INDEX"))
     (lambda (x) 
       (edbi:dbview-tabledef-create-buffer 
        conn table column-info pkey-info index-info)))))

(defun edbi:dbview-tabledef-get-pkey-info (pkey-info column-name)
  "[internal] "
  (loop with pkey-hrow = (car pkey-info)
        with pkey-rows = (cadr pkey-info)
        with pkname-f = (edbi:column-selector pkey-hrow "PK_NAME")
        with keyseq-f = (edbi:column-selector pkey-hrow "KEY_SEQ")
        with cname-f = (edbi:column-selector pkey-hrow "COLUMN_NAME")
        for row in pkey-rows
        for cname = (funcall cname-f row)
        if (equal column-name cname)
        return (format "%s %s" 
                       (funcall pkname-f row)
                       (funcall keyseq-f row))
        finally return ""))

(defun edbi:dbview-tabledef-create-buffer (conn table-name column-info pkey-info index-info)
  "[internal] "
  (let* ((buf (get-buffer-create edbi:dbview-table-buffer-name))
         (hrow (and column-info (car column-info)))
         (rows (and column-info (cadr column-info)))
         (data
          (loop with column-name-f = (edbi:column-selector hrow "COLUMN_NAME")
                with type-name-f   = (edbi:column-selector hrow "TYPE_NAME")
                with column-size-f = (edbi:column-selector hrow "COLUMN_SIZE")
                with nullable-f    = (edbi:column-selector hrow "NULLABLE")
                with remarks-f     = (edbi:column-selector hrow "REMARKS")
                for row in rows
                for column-name = (funcall column-name-f row)
                for type-name   = (funcall type-name-f row)
                for column-size = (funcall column-size-f row)
                for nullable    = (funcall nullable-f row)
                for remarks     = (funcall remarks-f row)
                collect
                (list column-name type-name 
                      (or column-size "")
                      (edbi:dbview-tabledef-get-pkey-info pkey-info column-name)
                      (if (equal nullable 0) "NOT NULL" "") (or remarks "")
                      row))) table-cp)
    (with-current-buffer buf
      (let (buffer-read-only)
        (erase-buffer)
        ;; header
        (insert (edbi:dbview-tabledef-header
                 (edbi:connection-ds conn) table-name data))
        ;; table
        (setq table-cp
              (ctbl:create-table-component-region
               :model
               (make-ctbl:model
                :column-model
                (list (make-ctbl:cmodel :title "Column Name" :align 'left)
                      (make-ctbl:cmodel :title "Type"    :align 'left)
                      (make-ctbl:cmodel :title "Size"    :align 'right)
                      (make-ctbl:cmodel :title "PKey"    :align 'left)
                      (make-ctbl:cmodel :title "Null"    :align 'left)
                      (make-ctbl:cmodel :title "Remarks" :align 'left))
                :data data
                :sort-state nil)
               :keymap edbi:dbview-table-keymap))
        ;; indexes
        (let ((index-rows (and index-info (cadr index-info))))
          (when index-rows
            (insert "\n"
                    (propertize (format "[Index: %s]\n" (length index-rows))
                                'face 'edbi:face-header))
            (loop for row in index-rows ; maybe index column (sqlite)
                  do (insert (format "- %s\n" (nth 5 row))))))

        (goto-char (point-min))
        (ctbl:cp-set-selected-cell table-cp '(0 . 0)))
      (setq buffer-read-only t)
      (current-buffer))))

(defun edbi:dbview-tabledef-show-data-command ()
  (interactive)
  (let ((args edbi:tabledef))
    (when args
      (destructuring-bind (conn catalog schema table-name) args
        (edbi:dbview-query-editor-open 
         conn 
         :init-sql (edbi:dbview-show-data-sql conn table-name)
         :executep t)))))

(defun edbi:dbview-tabledef-query-editor-command ()
  (interactive)
  (let ((args edbi:tabledef))
    (when args
      (destructuring-bind (conn catalog schema table-name) args
        (edbi:dbview-query-editor-open conn)))))

(defun edbi:dbview-tabledef-query-editor-new-command ()
  (interactive)
  (let ((args edbi:tabledef))
    (when args
      (destructuring-bind (conn catalog schema table-name) args
        (edbi:dbview-query-editor-open conn :force-create-p t)))))

(defun edbi:dbview-tabledef-quit-command ()
  (interactive)
  (let ((cbuf (current-buffer))
        (win-num (length (window-list))))
    (when (and (not (one-window-p))
               (> win-num edbi:before-win-num))
      (delete-window))
    (kill-buffer cbuf)))

(defun edbi:dbview-tabledef-update-command ()
  (interactive)
  (let ((args edbi:tabledef))
    (when args
      (apply 'edbi:dbview-tabledef-open args))))


;;; for auto-complete

(defface edbi:face-ac-table-candidate-face
  '((t (:background "lightgray" :foreground "navy")))
  "Face for table candidate"
  :group 'edbi)

(defface edbi:face-ac-table-selection-face
  '((t (:background "navy" :foreground "white")))
  "Face for the table selected candidate."
  :group 'edbi)

(defface edbi:face-ac-column-candidate-face
  '((t (:background "LightCyan" :foreground "DarkCyan")))
  "Face for column candidate"
  :group 'edbi)

(defface edbi:face-ac-column-selection-face
  '((t (:background "DarkCyan" :foreground "white")))
  "Face for the column selected candidate."
  :group 'edbi)

(defface edbi:face-ac-type-candidate-face
  '((t (:background "PaleGoldenrod" :foreground "DarkOliveGreen")))
  "Face for type candidate"
  :group 'edbi)

(defface edbi:face-ac-type-selection-face
  '((t (:background "DarkOliveGreen" :foreground "white")))
  "Face for the type selected candidate."
  :group 'edbi)

(defun edbi:setup-auto-complete ()
  "Initialization for auto-complete."
  (ac-define-source edbi:tables
    '((candidates . edbi:ac-editor-table-candidates)
      (candidate-face . edbi:face-ac-table-candidate-face)
      (selection-face . edbi:face-ac-table-selection-face)
      (symbol . "T")))
  (ac-define-source edbi:columns
    '((candidates . edbi:ac-editor-column-candidates)
      (candidate-face . edbi:face-ac-column-candidate-face)
      (selection-face . edbi:face-ac-column-selection-face)
      (symbol . "C")))
  (ac-define-source edbi:types
    '((candidates . edbi:ac-editor-type-candidates)
      (candidate-face . edbi:face-ac-type-candidate-face)
      (selection-face . edbi:face-ac-type-selection-face)
      (symbol . "+")))
  (ac-define-source edbi:keywords
    '((candidates . edbi:ac-editor-keyword-candidates)
      (symbol . "K")))
  (add-hook 'edbi:sql-mode-hook 'edbi:ac-edbi:sql-mode-hook)
  (add-hook 'edbi:dbview-update-hook 'edbi:ac-editor-word-candidate-update)
  (unless (memq 'edbi:sql-mode ac-modes)
    (setq ac-modes 
          (cons 'edbi:sql-mode ac-modes))))

(defun edbi:ac-edbi:sql-mode-hook ()
  (make-local-variable 'ac-sources)
  (setq ac-sources '(ac-source-words-in-same-mode-buffers
                     ac-source-edbi:tables
                     ac-source-edbi:columns
                     ac-source-edbi:types
                     ac-source-edbi:keywords)))

(defun edbi:ac-editor-table-candidates ()
  "Auto complete candidate function."
  (edbi:ac-candidates-tables (edbi:connection-ac edbi:connection)))

(defun edbi:ac-editor-column-candidates ()
  "Auto complete candidate function."
  (edbi:ac-candidates-columns (edbi:connection-ac edbi:connection)))

(defun edbi:ac-editor-type-candidates ()
  "Auto complete candidate function."
  (edbi:ac-candidates-types (edbi:connection-ac edbi:connection)))

(defun edbi:ac-editor-keyword-candidates ()
  "Auto complete candidate function."
  (edbi:ac-candidates-keywords (edbi:connection-ac edbi:connection)))

(defvar edbi:ac-editor-word-candidate-update-state nil "[internal] If t, the thread is working.")

(defun edbi:ac-editor-word-candidate-update-state-clear ()
  "[internal] "
  (interactive)
  (edbi:dbview-query-execute-semaphore-clear)
  (setq edbi:ac-editor-word-candidate-update-state nil))

(defun edbi:ac-editor-word-candidate-update (conn)
  "[internal] Start word collection for database information."
  (unless edbi:ac-editor-word-candidate-update-state
    (lexical-let ((conn conn) (dbd (edbi:dbd-get conn)) tables
                  (acs (make-edbi:ac-candidates)))
      (message "DB Word collection is started.")
      (setq edbi:ac-editor-word-candidate-update-state t)
      (deferred:try
        (edbi:seq
         (tables <- (edbi:ac-editor-word-candidate-update-tables conn dbd acs))
         (edbi:ac-editor-word-candidate-update-columns conn dbd acs tables)
         (edbi:ac-editor-word-candidate-update-types conn dbd acs)
         (edbi:ac-editor-word-candidate-update-keywords conn dbd acs))
        :finally
        (lambda (x) 
          (message "DB Word collection is finished.")
          (edbi:connection-ac-set conn acs)
          (setq edbi:ac-editor-word-candidate-update-state nil))))))

(defun edbi:ac-editor-word-candidate-update-tables (conn dbd acs)
  "[internal] "
  (lexical-let ((conn conn) (dbd dbd) (acs acs) table-info tables)
    (cc:semaphore-with edbi:dbview-query-execute-semaphore
      (lambda () 
        (edbi:seq
         (table-info <- (apply 'edbi:table-info-d conn
                               (funcall (edbi:dbd-table-info-args dbd) conn)))
         (lambda (x) 
           ;; return -> tables
           (edbi:ac-editor-word-candidate-update-tables1 conn dbd acs table-info)))))))

(defun edbi:ac-editor-word-candidate-update-tables1 (conn dbd acs table-info)
  "[internal] "
  (let (tables)
    (setf (edbi:ac-candidates-tables acs)
          (loop for (catalog schema table type remarks) in 
                (funcall (edbi:dbd-table-info-filter dbd) table-info)
                collect
                (progn
                  (push table tables)
                  (cons (propertize table 'summary type
                                    'document (format "%s\n%s" type remarks))
                        table))))
    tables))

(defun edbi:ac-editor-word-candidate-update-columns (conn dbd acs tables)
  "[internal] "
  (lexical-let ((conn conn) (dbd dbd) (acs acs)
                column-header column-rows
                (tables tables))
    (deferred:$
     (deferred:loop tables
       (lambda (table)
         (lexical-let ((table table))
           (cc:semaphore-with edbi:dbview-query-execute-semaphore
             (lambda (table)
               ;;(message "COLUMN--: %s" table)
               (deferred:nextc
                 (apply 'edbi:column-info-d conn
                        (funcall (edbi:dbd-column-info-args dbd) conn table))
                 (lambda (ci) 
                   ;;(message "COLUMN-INFO: %S" ci)
                   (unless column-header
                     (setq column-header (car ci)))
                   (setq column-rows
                         (append (cadr ci) column-rows)))))))))
     (deferred:nextc it
       (lambda (x) 
         (let ((column-info (list column-header column-rows)))
           ;;(message "COLUMN-INFO-ALL: %S" column-info)
           (edbi:ac-editor-word-candidate-update-columns1 conn dbd acs column-info)))))))

(defun edbi:ac-editor-word-candidate-update-columns1 (conn dbd acs column-info)
  "[internal] "
  (setf (edbi:ac-candidates-columns acs)
         (loop for (table-name column-name type-name column-size nullable remarks) in
               (funcall (edbi:dbd-column-info-filter dbd) column-info)
               collect
               (cons (propertize column-name 'summary table-name
                                 'document (format "%s %s %s\n%s" type-name
                                                   column-size nullable remarks))
                     column-name))) nil)

(defun edbi:ac-editor-word-candidate-update-types (conn dbd acs)
  "[internal] "
  (lexical-let ((conn conn) (dbd dbd) (acs acs) type-info)
    (cc:semaphore-with edbi:dbview-query-execute-semaphore
      (lambda () 
        (edbi:seq
         (type-info <- (edbi:type-info-all-d conn))
         (lambda (x) 
           ;;(message "TYPE-INFO: %S" type-info)
           (edbi:ac-editor-word-candidate-update-types1 conn dbd acs type-info)))))))

(defun edbi:ac-editor-word-candidate-update-types1 (conn dbd acs type-info)
  "[internal] "
  (setf (edbi:ac-candidates-types acs)
        (funcall (edbi:dbd-type-info-filter dbd) type-info)) nil)

(defun edbi:ac-editor-word-candidate-update-keywords (conn dbd acs)
  (setf (edbi:ac-candidates-keywords acs)
        (loop for (name . words) in (funcall (edbi:dbd-keywords dbd)) append
              (loop for word in words
                    collect
                    (cons (propertize word 'summary name
                                      'document name)
                          word)))) nil)

(eval-after-load 'auto-complete
  '(progn
     (edbi:setup-auto-complete)))

(edbi:dbd-init) ; init

(provide 'edbi)
;;; edbi.el ends here

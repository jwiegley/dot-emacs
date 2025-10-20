;;; org-mssql.el --- Secure MSSQL execution from Org-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Created: 19 Oct 2025
;; Version: 1.0
;; Keywords: org, sql, mssql
;; Package-Requires: ((emacs "27.1") (org "9.0"))

;;; Commentary:

;; This package provides helper functions for securely executing SQL queries
;; against Microsoft SQL Server from Org-mode literate programming files.
;;
;; It reads connection parameters from file-level Org properties, retrieves
;; passwords securely via auth-source, and constructs mssql-cli commands
;; suitable for Org-babel execution.
;;
;; Usage in Org files:
;;
;; Set file-level properties:
;;   #+PROPERTY: sql-host server.example.com
;;   #+PROPERTY: sql-user myuser
;;   #+PROPERTY: sql-port 1433
;;   #+PROPERTY: sql-database mydb
;;
;; Then in source blocks, use:
;;   #+begin_src sql :cmdline (org-mssql-get-cmdline)
;;   SELECT * FROM users;
;;   #+end_src
;;
;; Or for shell execution:
;;   #+begin_src sh :var params=(org-mssql-get-connection-params)
;;   echo "SELECT 1" | mssql-cli $params
;;   #+end_src

;;; Code:

(require 'org)
(require 'cl-lib)

(defgroup org-mssql nil
  "Secure MSSQL execution from Org-mode."
  :group 'org
  :prefix "org-mssql-")

(defcustom org-mssql-cli-executable "sqlcmd"
  "Path to the mssql-cli executable."
  :type 'file
  :group 'org-mssql)

(defcustom org-mssql-default-port 1433
  "Default port for SQL Server connections."
  :type 'integer
  :group 'org-mssql)

(defcustom org-mssql-password-lookup-function #'lookup-password
  "Function to retrieve passwords securely.
Should accept three arguments: HOST USER PORT.
Defaults to `lookup-password' which uses auth-source."
  :type 'function
  :group 'org-mssql)

;;; Internal variables

(defvar org-mssql--property-cache nil
  "Cache for Org file properties to avoid repeated lookups.")

;;; Core functions

(defun org-mssql--get-file-property (property)
  "Get file-level Org PROPERTY value from current buffer.
Uses `org-entry-get' with the 'file parameter to read global properties.
Caches results per buffer to improve performance."
  (unless (derived-mode-p 'org-mode)
    (error "Not in an Org-mode buffer"))

  (let* ((cache-key (cons (current-buffer) property))
         (cached-value (alist-get cache-key org-mssql--property-cache
                                  nil nil #'equal)))
    (if cached-value
        cached-value
      (when-let* ((value (org-entry-get nil property t)))
        (push (cons cache-key value) org-mssql--property-cache)
        value))))

(defun org-mssql--clear-property-cache ()
  "Clear the property cache.
Call this after modifying file-level Org properties."
  (interactive)
  (setq org-mssql--property-cache nil))

(defun org-mssql-get-connection-params ()
  "Retrieve SQL Server connection parameters from Org file properties.

Reads the following file-level properties:
  - sql-host: Server hostname or IP address (required)
  - sql-user: Username for authentication (required)
  - sql-port: Server port (optional, defaults to 1433)
  - sql-database: Database name (required)

Returns a plist with keys:
  :host :user :port :database :password

Signals an error if required properties are missing or if password
retrieval fails."
  (let* ((host (org-mssql--get-file-property "sql-host"))
         (user (org-mssql--get-file-property "sql-user"))
         (port (or (when-let* ((p (org-mssql--get-file-property "sql-port")))
                     (string-to-number p))
                   org-mssql-default-port))
         (database (org-mssql--get-file-property "sql-database")))

    ;; Validate required parameters
    (unless host
      (error "Missing required property: sql-host"))
    (unless user
      (error "Missing required property: sql-user"))
    (unless database
      (error "Missing required property: sql-database"))

    ;; Retrieve password securely
    (condition-case err
        (let ((password (funcall org-mssql-password-lookup-function
                                host user port)))
          (unless password
            (error "Password not found in auth-source for %s@%s:%d"
                   user host port))

          (list :host host
                :user user
                :port port
                :database database
                :password password))
      (error
       (error "Failed to retrieve connection parameters: %s"
              (error-message-string err))))))

(defun org-mssql--build-cmdline (params)
  "Build mssql-cli command line arguments from PARAMS plist.

PARAMS should contain:
  :host :user :port :database :password

Returns a string suitable for passing to mssql-cli via :cmdline
in Org-babel source blocks.

Security note: The password is included in the command line, which
may be visible in process listings. For production use, consider
using environment variables or connection strings."
  (let ((host (plist-get params :host))
        (user (plist-get params :user))
        (port (plist-get params :port))
        (database (plist-get params :database))
        (password (plist-get params :password)))

    (format "-S %s,%d -U %s -P %s -d %s"
            (shell-quote-argument host)
            port
            (shell-quote-argument user)
            (shell-quote-argument password)
            (shell-quote-argument database))))

(defun org-mssql-get-cmdline ()
  "Get complete mssql-cli command line for use in Org-babel :cmdline.

Combines connection parameters from file-level Org properties with
password retrieval to construct a secure connection string.

Usage in Org source blocks:
  #+begin_src sql :cmdline (org-mssql-get-cmdline)
  SELECT * FROM table;
  #+end_src

Returns a string with all necessary mssql-cli arguments."
  (org-mssql--build-cmdline (org-mssql-get-connection-params)))

(defun org-mssql-get-connection-string ()
  "Get connection parameters as a shell-safe string for piping queries.

Returns a space-separated string of connection parameters suitable
for use in shell commands:
  -S host,port -U user -P password -d database

Usage in Org source blocks:
  #+begin_src sh :var params=(org-mssql-get-connection-string)
  echo \"SELECT 1\" | mssql-cli $params
  #+end_src

Security warning: This exposes the password in the command line.
Use with caution in multi-user environments."
  (org-mssql-get-cmdline))

(defun org-mssql-test-connection ()
  "Test the SQL Server connection using current Org file properties.

Executes a simple SELECT 1 query to verify connectivity and
authentication. Displays the result in the echo area.

Useful for debugging connection issues before executing complex queries."
  (interactive)
  (condition-case err
      (let* ((params (org-mssql-get-connection-params))
             (cmdline (org-mssql--build-cmdline params))
             (cmd (format "echo 'SELECT 1 AS test;' | %s %s"
                         org-mssql-cli-executable
                         cmdline)))
        (message "Testing connection to %s@%s:%d..."
                 (plist-get params :user)
                 (plist-get params :host)
                 (plist-get params :port))

        (with-temp-buffer
          (let ((exit-code (call-process-shell-command cmd nil t)))
            (if (zerop exit-code)
                (message "Connection successful: %s" (buffer-string))
              (error "Connection failed (exit code %d): %s"
                     exit-code (buffer-string))))))
    (error
     (message "Connection test failed: %s" (error-message-string err)))))

(defun org-mssql-insert-template ()
  "Insert a template for MSSQL connection properties at point.

Inserts file-level property definitions for SQL Server connection
parameters that can be customized for the current document."
  (interactive)
  (insert "#+PROPERTY: sql-host server.example.com\n"
          "#+PROPERTY: sql-user myuser\n"
          "#+PROPERTY: sql-port 1433\n"
          "#+PROPERTY: sql-database mydb\n"
          "\n"
          "# Example SQL block:\n"
          "#+begin_src sql :cmdline (org-mssql-get-cmdline) :results table\n"
          "SELECT TOP 10 * FROM sys.tables;\n"
          "#+end_src\n"))

;;; Utility functions

(defun org-mssql-get-current-database ()
  "Return the database name from current Org file properties.
Convenience function for displaying or using the database name."
  (interactive)
  (if-let* ((db (org-mssql--get-file-property "sql-database")))
      (progn
        (when (called-interactively-p 'interactive)
          (message "Current database: %s" db))
        db)
    (error "No sql-database property defined")))

(defun org-mssql-show-connection-info ()
  "Display current connection information (without password).

Shows the host, user, port, and database configured in the
current Org file. Useful for verifying configuration before
executing queries."
  (interactive)
  (condition-case err
      (let* ((host (org-mssql--get-file-property "sql-host"))
             (user (org-mssql--get-file-property "sql-user"))
             (port (or (org-mssql--get-file-property "sql-port")
                      (number-to-string org-mssql-default-port)))
             (database (org-mssql--get-file-property "sql-database")))

        (message "Connection: %s@%s:%s/%s"
                 (or user "?")
                 (or host "?")
                 port
                 (or database "?")))
    (error
     (message "Error reading connection info: %s"
              (error-message-string err)))))

;;; Mode integration

(defvar org-mssql-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c m t") #'org-mssql-test-connection)
    (define-key map (kbd "C-c m i") #'org-mssql-show-connection-info)
    (define-key map (kbd "C-c m c") #'org-mssql--clear-property-cache)
    map)
  "Keymap for `org-mssql-mode'.")

;;;###autoload
(define-minor-mode org-mssql-mode
  "Minor mode for working with MSSQL in Org-mode files.

Provides convenient key bindings for testing connections and
viewing configuration:

\\{org-mssql-mode-map}"
  :lighter " MSSQL"
  :keymap org-mssql-mode-map
  :group 'org-mssql
  (when org-mssql-mode
    ;; Clear cache when mode is enabled to ensure fresh data
    (org-mssql--clear-property-cache)))

;;; Hooks

(defun org-mssql--invalidate-cache-on-save ()
  "Clear property cache when Org file is saved.
This ensures properties are re-read after modifications."
  (when (and (derived-mode-p 'org-mode)
             org-mssql-mode)
    (org-mssql--clear-property-cache)))

(add-hook 'after-save-hook #'org-mssql--invalidate-cache-on-save)

(provide 'org-mssql)

;;; org-mssql.el ends here

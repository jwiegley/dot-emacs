;;; prodigy-services --- Service definitions for Prodigy -*- lexical-binding: t -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 23 Jun 2025
;; Version: 1.0
;; Keywords: ai gptel tools
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Code:

(require 'prodigy)

(defun prodigy-service--build-tunnel-args (args)
  "Assemble the ssh tunnel argument list from ARGS."
  `("-v" ;; allows us to parse for the ready message
    ;; "-N" ;; don't start an interactive shell remotely
    "-L" ,(concat (plist-get args :local-port) ":"
                  (plist-get args :remote-ip) ":"
                  (plist-get args :remote-port))
    ,(plist-get args :host)))    ;; the remote host

(prodigy-define-tag
  :name 'ssh-tunnel
  :command "ssh"
  :cwd (getenv "HOME")
  :args (prodigy-callback (service)
          (prodigy-service--build-tunnel-args
           (plist-get service :tunnel)))
  :ready-message "debug1: Entering interactive session.")

(prodigy-define-service
  :name "SillyTavern tunnel"
  :tags '(ssh-tunnel)
  :tunnel '(
            :local-port "8083"
            :remote-ip "127.0.0.1"
            :remote-port "8083"
            :host "vulcan"
            ))

(prodigy-define-service
  :name "MLX-LM"
  :command "mlx-lm"
  :cwd "~/Models"
  :args '("server"
          "--model" "mlx-community/???"
          "--port" "8082")
  :port 8082)

(let ((model-path
       "~/Models/unsloth_gemma-3-12b-it-GGUF/gemma-3-12b-it-UD-Q8_K_XL.gguf"))
  (prodigy-define-service
    :name "llama-cpp"
    :command "llama-server"
    :cwd "~/Models"
    :args `("--jinja"
            "--model" ,(expand-file-name model-path)
            "--port" "8081")
    :port 8081))

(provide 'prodigy-services)

;;; prodigy-services.el ends here

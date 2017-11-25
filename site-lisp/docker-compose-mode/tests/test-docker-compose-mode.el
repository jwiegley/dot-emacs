;;; test-docker-compose-mode.el --- Tests for docker-compose-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Ricardo Martins

;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at
;;
;; http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.

;;; Code:

(require 'docker-compose-mode)

(describe "Function: `docker-compose--prefix'"
  (it "returns the partially written key in the current line"
    (with-temp-buffer
      (insert "version: '2'\nservices:\n  example:\n    underscore_\n    partial")
      ;; move point to after the underscore
      (goto-char 50)
      (expect (docker-compose--prefix) :to-equal '("underscore_" 39 50))))

  (describe "when the key is suffixed with a colon"
    (it "returns nil"
      (with-temp-buffer
        (insert "  foo:")
        (goto-char 7)
        (expect (docker-compose--prefix) :to-equal nil))))

  (describe "when the current partially written key is a top-level key"
    (it "returns it"
      (with-temp-buffer
        (insert "version: '2'\nservices:\n  consumer:\n    build: .\n\n  web:\n    image: foo\n\nnet")
        (goto-char 76)
        (expect (docker-compose--prefix) :to-equal '("net" 73 76))))))

(describe "Function: `docker-compose--candidates'"
  (let ((candidates '(("version") ("services" ("^[a-zA-Z0-9._-]+$" ("build" ("context") ("dockerfile") ("args" (".+"))) ("cap_add") ("cap_drop") ("cgroup_parent") ("command") ("container_name") ("cpu_shares") ("cpu_quota") ("cpuset") ("depends_on") ("devices") ("dns") ("dns_opt") ("dns_search") ("domainname") ("entrypoint") ("env_file") ("environment" (".+")) ("expose") ("extends" ("service") ("file")) ("external_links") ("extra_hosts" (".+")) ("hostname") ("image") ("ipc") ("labels" (".+")) ("links") ("logging" ("driver") ("options")) ("mac_address") ("mem_limit") ("mem_reservation") ("mem_swappiness") ("memswap_limit") ("network_mode") ("networks" ("^[a-zA-Z0-9._-]+$" ("aliases") ("ipv4_address") ("ipv6_address"))) ("oom_score_adj") ("group_add") ("pid") ("ports") ("privileged") ("read_only") ("restart") ("security_opt") ("shm_size") ("stdin_open") ("stop_grace_period") ("stop_signal") ("tmpfs") ("tty") ("ulimits" ("^[a-z]+$" ("hard") ("soft"))) ("user") ("volumes") ("volume_driver") ("volumes_from") ("working_dir"))) ("networks" ("^[a-zA-Z0-9._-]+$" ("driver") ("driver_opts" ("^.+$")) ("ipam" ("driver") ("config") ("options" ("^.+$"))) ("external" ("name")) ("internal"))) ("volumes" ("^[a-zA-Z0-9._-]+$" ("driver") ("driver_opts" ("^.+$")) ("external" ("name")))))))

    (it "returns all the applicable candidates"
      (spy-on 'docker-compose--keywords-for-buffer :and-return-value candidates)
      (spy-on 'docker-compose--find-context :and-return-value '("services" "web"))
      (let ((expected-candidates '("env_file" "environment")))
        (expect (docker-compose--candidates "env") :to-equal expected-candidates)))

    (describe "when the buffer version is invalid"
      (it "returns nil"
        (with-temp-buffer
          (insert "version: 2\nservices:\n  consumer:\n    build: .\n\n  web:\n    image: foo\n\nnet")
          (goto-char 74)
          (expect (docker-compose--candidates "net") :to-equal nil))))

    (describe "when no applicable candidates are available"
      (it "returns nil"
        (spy-on 'docker-compose--keywords-for-buffer '())
        (expect (docker-compose--candidates "en") :to-equal nil)))

    (describe "when the prefix is a top-level key"
      (it "returns all the applicable top-level candidates"
        (with-temp-buffer
          (insert "version: '2'\nservices:\n  consumer:\n    build: .\n\n  web:\n    image: foo\n\nnet")
          (goto-char 76)
          (expect (docker-compose--prefix) :to-equal '("net" 73 76))
          (expect (docker-compose--candidates "net") :to-equal '("networks")))))

    (describe "when the parent context has a 'oneOf' property"
      (it "returns all the applicable candidates"
        (spy-on 'docker-compose--keywords-for-buffer :and-return-value candidates)
        (with-temp-buffer
          (insert "version: \"2\"\n\nservices:\n  common: &BASE\n    build:\n      con\n      args:\n        BUNDLE_GITHUB__COM: ${BUNDLE_GITHUB__COM}\n")
          (goto-char 61)
          (expect (docker-compose--prefix) :to-equal '("con" 58 61))
          (expect (docker-compose--find-context) :to-equal '("services" "common" "build"))
          (expect (docker-compose--candidates "con") :to-equal '("context")))))

    (describe "when the prefix is empty"
      (it "returns all the applicable candidates"
        (spy-on 'docker-compose--keywords-for-buffer :and-return-value candidates)
        (with-temp-buffer
          (insert "version: \"2\"\n\nservices:\n  common: &BASE\n    build:\n      \n      context: .\n      args:\n        BUNDLE_GITHUB__COM: ${BUNDLE_GITHUB__COM}\n")
          (goto-char 58)
          (expect (docker-compose--prefix) :to-equal nil)
          (expect (docker-compose--find-context) :to-equal '("services" "common" "build"))
          (expect (docker-compose--candidates nil) :to-equal '("context" "dockerfile" "args")))))))

(describe "Function: `docker-compose--find-context'"
  (it "returns a list with the ancestor keywords"
    (with-temp-buffer
      (insert "version: '2'\nservices:\n  web:\n    image: foo\n    env")
      (goto-char 53)
      (expect (docker-compose--prefix) :to-equal '("env" 50 53))
      (expect (docker-compose--find-context) :to-equal '("services" "web")))
    (with-temp-buffer
      (insert "version: '2'\nservices:\n  consumer:\n    build: .\n\n  web:\n    image: foo\n    env")
      (goto-char 79)
      (expect (docker-compose--prefix) :to-equal '("env" 76 79))
      (expect (docker-compose--find-context) :to-equal '("services" "web")))
    (with-temp-buffer
      (insert "version: '2'\nservices:\n  consumer:\n    build: .\n\n  web:\n    image: foo\n")
      (goto-char 72)
      (expect (docker-compose--prefix) :to-equal nil)
      (expect (docker-compose--find-context) :to-equal '()))))

(describe "Function: `docker-compose--find-version'"
  (describe "when the version is not specified"
    (it "returns \"1.0\""
      (with-temp-buffer
        (insert "services:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal "1.0"))))

  (describe "when the version is surrounded by a single quote and a double quote"
    (it "returns nil"
      (with-temp-buffer
        (insert "version: '2\"\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal nil))))

  (describe "when the version is surrounded by a double quote and a single quote"
    (it "returns nil"
      (with-temp-buffer
        (insert "version: \"2'\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal nil))))

  (describe "when the version is not surrounded by quotes"
    (it "returns nil"
      (with-temp-buffer
        (insert "version: 2\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal nil))))

  (describe "when the version is surrounded by single quotes"
    (it "returns the version specified by the `version' key"
      (with-temp-buffer
        (insert "version: '2'\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal "2"))))

  (describe "when the version is surrounded by double quotes"
    (it "returns the version specified by the `version' key"
      (with-temp-buffer
        (insert "version: \"2\"\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal "2"))))

  (describe "when the version contains a major and a minor part"
    (it "returns the major and the minor"
      (with-temp-buffer
        (insert "version: \"3.3\"\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal "3.3"))))

  (describe "when the version contains a major part, a minor part, and a suffix"
    (it "returns it"
      (with-temp-buffer
        (insert "version: \"3.4-beta\"\nservices:\n  foo:\n    build: .\n")
        (expect (docker-compose--find-version) :to-equal "3.4-beta")))))

(provide 'test-docker-compose-mode)
;;; test-docker-compose-mode.el ends here

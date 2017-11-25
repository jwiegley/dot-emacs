(require 'org-trello-entity)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-entity-comment-description-region ()
  (should (equal '(49 85)
                 (orgtrello-tests-with-temp-buffer
                  "* card
** COMMENT, tony date
:PROPERTIES:
:END:
  comment's description
  ends here

* another card
"
                  (orgtrello-entity-comment-description-region)
                  -7)))

  (should (equal '(30 66)
                 (orgtrello-tests-with-temp-buffer
                  "* card
** COMMENT, tony date
  comment's description
  ends here

* another card
"
                  (orgtrello-entity-comment-description-region)
                  -5))))

(ert-deftest test-orgtrello-entity-comment-description-end-point ()
  (should (eq 85
              (orgtrello-tests-with-temp-buffer
               "* card
** COMMENT, tony date
:PROPERTIES:
:END:
  comment's description
  ends here

* another card
"
               (orgtrello-entity-comment-description-end-point)
               -7)))

  (should (eq 66
              (orgtrello-tests-with-temp-buffer
               "* card
** COMMENT, tony date
  comment's description
  ends here

* another card
"
               (orgtrello-entity-comment-description-end-point)
               -5))))
(ert-deftest test-orgtrello-entity-comment-description-start-point ()
  (should (eq 49
              (orgtrello-tests-with-temp-buffer
               "* card
** COMMENT, tony date
:PROPERTIES:
:END:
  comment's description
* another card
"
               (orgtrello-entity-comment-description-start-point)
               -5)))
  (should (eq 30
              (orgtrello-tests-with-temp-buffer
               "* card
** COMMENT, tony date
  comment's description
* another card
"
               (orgtrello-entity-comment-description-start-point)
               -3))))

(ert-deftest test-orgtrello-entity-compute-first-comment-point ()
  (should (eq 47
              (orgtrello-tests-with-temp-buffer
               "* card
description
  - [ ] cbx
    - [ ] item
** COMMENT user, date
"
               (orgtrello-entity-compute-first-comment-point))))
  (should (eq 8
              (orgtrello-tests-with-temp-buffer
               "* card
** COMMENT user, date
"
               (orgtrello-entity-compute-first-comment-point))))
  ;; no comment, return the card's end region
  (should (eq 8
              (orgtrello-tests-with-temp-buffer
               "* card
"
               (orgtrello-entity-compute-first-comment-point)))))

(ert-deftest test-orgtrello-entity-card-description-start-point ()
  (should (eq 8
              (orgtrello-tests-with-temp-buffer
               "* card
description"
               (orgtrello-entity-card-description-start-point))))
  (should (eq 8
              (orgtrello-tests-with-temp-buffer
               "* card
  description"
               (orgtrello-entity-card-description-start-point))))
  (should (eq 27
              (orgtrello-tests-with-temp-buffer
               "* card
:PROPERTIES:
:END:
description
"
               (orgtrello-entity-card-description-start-point))))
  (should (eq 27
              (orgtrello-tests-with-temp-buffer "* card
:PROPERTIES:
:END:
  description
"
                                                (orgtrello-entity-card-description-start-point)))))

(ert-deftest test-orgtrello-entity-card-metadata-end-point ()
  ;; we are getting just before the card's checklist
  (should (eq 34
              (orgtrello-tests-with-temp-buffer
               "* card
:PROPERTIES:
:END:
  desc

  - [ ] chcklist
* another card"
               (progn
                 (goto-char (point-min))
                 (orgtrello-entity-card-metadata-end-point)))))

  ;; hitting another heading returns 1 point before it
  (should (eq 7
              (orgtrello-tests-with-temp-buffer
               "* card
* another card"
               (progn
                 (goto-char (point-min))
                 (orgtrello-entity-card-metadata-end-point)))))

  ;; hitting the end of the buffer returns the end of buffer
  (should (eq 7 (orgtrello-tests-with-temp-buffer
                 "* card
"
                 (progn
                   (goto-char (point-min))
                   (orgtrello-entity-card-metadata-end-point))))))

(ert-deftest test-orgtrello-entity-goto-end-card-metadata ()
  ;; we are getting just before the card's checklist
  (should (string=
           "  - [ ] chcklist"
           (orgtrello-tests-with-temp-buffer
            "* card
:PROPERTIES:
:END:
  desc

  - [ ] chcklist
* another card"
            (progn
              (goto-char (point-min))
              (orgtrello-entity-goto-end-card-metadata)
              (buffer-substring-no-properties (point) (point-at-eol))))))

  ;; hitting another heading returns nil
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
* another card"
               (progn
                 (goto-char (point-min))
                 (orgtrello-entity-goto-end-card-metadata))))
  ;; hitting the end of the buffer returns nil
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
"
               (progn
                 (goto-char (point-min))
                 (orgtrello-entity-goto-end-card-metadata)))))

(ert-deftest test-orgtrello-entity-goto-next-checkbox ()
  (defun string-at-pt ()
    "Extract string at point."
    (buffer-substring-no-properties (point-at-bol)
                                    (point-at-eol)))
  (should (equal
           '("  - [ ] checkbox 1"
             "    - [ ] item 1"
             "    - [ ] item 2"
             "  - [ ] checkbox 2"
             "")
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checkbox 1
    - [ ] item 1
    - [ ] item 2
  - [ ] checkbox 2
"
            (let* ((trail nil)
                   (cbx-start (push (string-at-pt) trail)))
              (orgtrello-entity-goto-next-checkbox)
              (push (string-at-pt) trail)
              (orgtrello-entity-goto-next-checkbox)
              (push (string-at-pt) trail)
              (orgtrello-entity-goto-next-checkbox)
              (push (string-at-pt) trail)
              (orgtrello-entity-goto-next-checkbox)
              (push (string-at-pt) trail)
              (nreverse trail))
            -4))))

(ert-deftest test-orgtrello-entity-goto-next-checkbox-with-same-level ()
  (defun string-at-pt ()
    "Extract string at point."
    (buffer-substring-no-properties (point-at-bol)
                                    (point-at-eol)))
  (should (equal
           '("  - [ ] checkbox 1"
             "  - [ ] checkbox 2"
             "")
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checkbox 1
    - [ ] item 1
    - [ ] item 2
  - [ ] checkbox 2
"
            (let* ((trail nil)
                   (cbx-start (push (string-at-pt) trail)))
              (orgtrello-entity-goto-next-checkbox-with-same-level 2)
              (push (string-at-pt) trail)
              (orgtrello-entity-goto-next-checkbox-with-same-level 2)
              (push (string-at-pt) trail)
              (nreverse trail))
            -4)))

  (should (equal
           '("    - [X] item 1"
             "    - [ ] item 2"
             "")
           (orgtrello-tests-with-temp-buffer
            "* card
  - [ ] checkbox 1
    - [X] item 1
    - [ ] item 2
  - [ ] checkbox 2
"
            (let* ((trail nil)
                   (cbx-start (push (string-at-pt) trail)))
              (orgtrello-entity-goto-next-checkbox-with-same-level 3)
              (push (string-at-pt) trail)
              (orgtrello-entity-goto-next-checkbox-with-same-level 3)
              (push (string-at-pt) trail)
              (nreverse trail))
            -3))))


(ert-deftest test-orgtrello-entity-card-start-point ()
  (should (eq 32
              (orgtrello-tests-with-temp-buffer
               ":PROPERTIES:
...
:END:

* card
* another card
"
               (orgtrello-entity-card-start-point))))
  (should (eq 25
              (orgtrello-tests-with-temp-buffer
               ":PROPERTIES:
...
:END:

* card
* another card
"
               (orgtrello-entity-card-start-point)
               -2))))

(ert-deftest test-orgtrello-entity-org-checkbox-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
    - [ ] ok for item
"
           (orgtrello-entity-org-checkbox-p)))
  (should (orgtrello-tests-with-temp-buffer
           "* card
  - [ ] ok for checklist
"
           (orgtrello-entity-org-checkbox-p)))
  (should (orgtrello-tests-with-temp-buffer
           "* card
- [ ] checkbox ok
"
           (orgtrello-entity-org-checkbox-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
"
               (orgtrello-entity-org-checkbox-p))))

(ert-deftest test-orgtrello-entity-org-heading-with-level-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
"
           (orgtrello-entity-org-heading-with-level-p org-trello--card-level)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
"
               (orgtrello-entity-org-heading-with-level-p org-trello--card-level)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
  - [ ] item
"
               (orgtrello-entity-org-heading-with-level-p org-trello--card-level))))

(ert-deftest test-orgtrello-entity-org-card-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
"
           (orgtrello-entity-org-card-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
"
               (orgtrello-entity-org-card-p)))

  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
  - [ ] item
"
               (orgtrello-entity-org-card-p))))

(ert-deftest test-orgtrello-entity--org-checkbox-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
- [ ] checklist
"
           (orgtrello-entity--org-checkbox-p 0)))
  (should (orgtrello-tests-with-temp-buffer
           "* card
- [ ] checklist
  - [ ] item
"
           (orgtrello-entity--org-checkbox-p 2)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
"
               (orgtrello-entity--org-checkbox-p 2)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
"
               (orgtrello-entity--org-checkbox-p 2))))

(ert-deftest test-orgtrello-entity-org-checklist-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
  - [ ] checklist
"
           (orgtrello-entity-org-checklist-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
"
               (orgtrello-entity-org-checklist-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
"
               (orgtrello-entity-org-checklist-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
  - [ ] checklist
    - [ ] item
"
               (orgtrello-entity-org-checklist-p))))

(ert-deftest test-orgtrello-entity-org-item-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
  - [ ] checklist
    - [ ] item
"
           (orgtrello-entity-org-item-p)))

  (should-not (orgtrello-tests-with-temp-buffer
               "* card
"
               (orgtrello-entity-org-item-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
  - [ ] checklist
"
               (orgtrello-entity-org-item-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
- [ ] checklist
  - [ ] item
"
               (orgtrello-entity-org-item-p))))

(ert-deftest test-orgtrello-entity-org-comment-p ()
  (should (orgtrello-tests-with-temp-buffer
           "* card
  - [ ] checklist
    - [ ] item
** COMMENT ardumont:
booyah
"
           (orgtrello-entity-org-comment-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
"
               (orgtrello-entity-org-comment-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
  - [ ] checklist
"
               (orgtrello-entity-org-comment-p)))
  (should-not (orgtrello-tests-with-temp-buffer
               "* card
  - [ ] checklist
    - [ ] item
"
               (orgtrello-entity-org-comment-p))))

(ert-deftest test-orgtrello-entity-level ()
  ;; ok
  (should (equal 1  (orgtrello-tests-with-temp-buffer "* some card" (orgtrello-entity-level))))
  (should (equal 2  (orgtrello-tests-with-temp-buffer "  - [X] some checkbox :PROPERTIES: {\"orgtrello-id\":\"123\"}" (orgtrello-entity-level))))
  (should (equal 3  (orgtrello-tests-with-temp-buffer "    - [X] some checkbox :PROPERTIES: {\"orgtrello-id\":\"123\"}" (orgtrello-entity-level))))
  ;; ko
  (should (equal -1 (orgtrello-tests-with-temp-buffer "* card\n - [X] some checkbox :PROPERTIES: {\"orgtrello-id\":\"123\"}" (orgtrello-entity-level) 0)))
  (should (equal -1 (orgtrello-tests-with-temp-buffer "* card\n     - [X] some checkbox :PROPERTIES: {\"orgtrello-id\":\"123\"}" (orgtrello-entity-level) 0))))

(ert-deftest test-orgtrello-entity-card-at-pt ()
  (should (equal t
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
   DEADLINE: <2014-04-01T00:00:00.000Z>
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
hello there
"
                                                   (orgtrello-entity-card-at-pt))))

  (should (equal nil
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}"
                                                   (orgtrello-entity-card-at-pt)
                                                   0)))
  (should (equal nil
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}"
                                                   (orgtrello-entity-card-at-pt)
                                                   0))))

(ert-deftest test-orgtrello-entity-checklist-at-pt ()
  (should (equal nil
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
   DEADLINE: <2014-04-01T00:00:00.000Z>
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
hello there
"
                                                   (orgtrello-entity-checklist-at-pt))))

  (should (equal t
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}"
                                                   (orgtrello-entity-checklist-at-pt)
                                                   0)))
  (should (equal nil
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}"
                                                   (orgtrello-entity-checklist-at-pt)
                                                   0))))

(ert-deftest test-orgtrello-entity-item-at-pt ()
  (should (equal nil
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
   DEADLINE: <2014-04-01T00:00:00.000Z>
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
hello there
"
                                                   (orgtrello-entity-item-at-pt))))

  (should (equal nil
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}"
                                                   (orgtrello-entity-item-at-pt)
                                                   0)))
  (should (equal t
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}"
                                                   (orgtrello-entity-item-at-pt)
                                                   0))))

(ert-deftest test-orgtrello-entity-compute-checklist-header-region ()
  (should (equal '(8 24)
                 (orgtrello-tests-with-temp-buffer
                  "* card
- [ ] checklist
- [ ] another"
                  (orgtrello-entity-compute-checklist-header-region)))))

(ert-deftest test-orgtrello-entity-compute-checklist-region ()
  (should (equal '(8 25)
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
  - [ ] another checklist"
                  (orgtrello-entity-compute-checklist-region))))
  (should (equal "  - [ ] checklist"
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
  - [ ] another checklist"
                  (apply 'buffer-substring-no-properties (orgtrello-entity-compute-checklist-region)))))
  (should (equal '(8 40)
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item
"
                  (orgtrello-entity-compute-checklist-region))))
  (should (equal '(8 53)
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item
    - item 2
"
                  (orgtrello-entity-compute-checklist-region)
                  -3)))
  (should (equal '(8 53)
                 (orgtrello-tests-with-temp-buffer
                  "* card
  - [ ] checklist
    - [ ] item
    - item 2
* another card"
                  (orgtrello-entity-compute-checklist-region)
                  -3))))

(ert-deftest test-orgtrello-entity-compute-item-region ()
  (should (equal '(17 32)
                 (orgtrello-tests-with-temp-buffer "- [ ] checklist\n  - [ ] another" (orgtrello-entity-compute-item-region) 0))))

(ert-deftest test-orgtrello-entity-next-checklist-point ()
  (should (equal 24 (orgtrello-tests-with-temp-buffer "* card\n- [ ] checkbox 0\n- [ ] checkbox 1\n" (orgtrello-entity-next-checklist-point) -2)))
  (should (equal 55 (orgtrello-tests-with-temp-buffer "* card\n- [ ] checkbox 0\n  - [ ] item0\n- [ ] checkbox 1\n" (orgtrello-entity-next-checklist-point) -1))))

(ert-deftest test-orgtrello-entity-card-end-point ()
  (should (equal 50 (orgtrello-tests-with-temp-buffer "* heading\n- [ ] some checklist\n  - [ ] some item\n"                                      (orgtrello-entity-card-end-point)))) ;; return the max point
  (should (equal 70 (orgtrello-tests-with-temp-buffer "#+TODO: TODO | DONE\n* heading\n- [ ] some checklist\n  - [ ] some item\n"                 (orgtrello-entity-card-end-point)))) ;; return the max point
  (should (equal 65 (orgtrello-tests-with-temp-buffer "* heading\n- [ ] some checklist\n  - [ ] some item\n* next heading\n"                      (orgtrello-entity-card-end-point))))
  (should (equal 85 (orgtrello-tests-with-temp-buffer "#+TODO: TODO | DONE\n* heading\n- [ ] some checklist\n  - [ ] some item\n* next heading\n" (orgtrello-entity-card-end-point))))
  (should (equal 70 (orgtrello-tests-with-temp-buffer "#+TODO: TODO | DONE\n* heading\n- [ ] some checklist\n  - [ ] some item\n* next heading\n" (orgtrello-entity-card-end-point) -3)))
  (should (equal 70 (orgtrello-tests-with-temp-buffer "#+TODO: TODO | DONE\n* heading\n- [ ] some checklist\n  - [ ] some item\n* next heading\n" (orgtrello-entity-card-end-point) -4))))

(ert-deftest test-orgtrello-entity-card-region ()
  "Compute the region of the card."
  (should (equal
           '(1 265)
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card"
                                             (orgtrello-entity-card-region)
                                             -2)))
  (should (equal
           '(265 279)
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card"
                                             (orgtrello-entity-card-region)
                                             0)))
  (should (equal
           "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
"
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card"
                                             (apply 'buffer-substring-no-properties (orgtrello-entity-card-region))
                                             -2)))
  (should (equal
           "* another card"
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card"
                                             (apply 'buffer-substring-no-properties (orgtrello-entity-card-region))
                                             0))))


(ert-deftest test-orgtrello-entity-card-metadata-region ()
  (should (equal
           "  hello there"
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card"
                                             (apply 'buffer-substring-no-properties (orgtrello-entity-card-metadata-region))
                                             -2))))


(ert-deftest test-orgtrello-entity-card-data-region ()
  (should (equal
           "- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}"
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card"
                                             (apply 'buffer-substring-no-properties (orgtrello-entity-card-data-region))
                                             -2))))

(ert-deftest test-orgtrello-entity-comment-region ()
  (should (equal
           "** COMMENT ardumont, 2014-12-09T17:29:42.073Z
:PROPERTIES:
:orgtrello-id: 548731866513c90940aa7746
:END:
ardumont comment
"
           (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
- [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
  - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
* another card
** COMMENT ardumont, 2014-12-09T17:29:42.073Z
:PROPERTIES:
:orgtrello-id: 548731866513c90940aa7746
:END:
ardumont comment
"
                                             (apply 'buffer-substring-no-properties (orgtrello-entity-comment-region))
                                             -2))))

(ert-deftest test-orgtrello-entity-comment-at-pt ()
  (should-not (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
   DEADLINE: <2014-04-01T00:00:00.000Z>
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
hello there
"
                                                (orgtrello-entity-org-comment-p)))
  (should (equal t
                 (orgtrello-tests-with-temp-buffer "* TODO Joy of FUN(ctional) LANGUAGES
:PROPERTIES:
:orgtrello-id: 52c945143004d4617c012528
:END:
  hello there
  - [-] LISP family   :PROPERTIES: {\"orgtrello-id\":\"52c945140a364c5226007314\"}
    - [X] Emacs-Lisp  :PROPERTIES: {\"orgtrello-id\":\"52c9451784251e1b260127f8\"}
** COMMENT ardumont, some-date
hello"
                                                   (orgtrello-entity-org-comment-p)
                                                   0))))


(provide 'org-trello-entity-test)
;;; org-trello-entity-test.el ends here

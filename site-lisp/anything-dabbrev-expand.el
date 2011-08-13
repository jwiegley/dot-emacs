;;; anything-dabbrev-expand.el --- dabbrev-expand / dabbrev-completion / partial-dabbrev using anything.el
;; $Id: anything-dabbrev-expand.el,v 1.20 2009/04/20 16:26:43 rubikitch Exp rubikitch $

;; Copyright (C) 2008  rubikitch

;; Author: rubikitch <rubikitch@ruby-lang.org>
;; Keywords: dabbrev, convenience, anything
;; URL: http://www.emacswiki.org/cgi-bin/wiki/download/anything-dabbrev-expand.el

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Dynamic abbrev for multiple selection using `anything', and partial dabbrev.
;; This package is tested on Emacs 22.

;;; Commands:
;;
;; Below are complete command list:
;;
;;  `anything-dabbrev-expand'
;;    The command does dynamic abbrev expansion for multiple selection using `anything'.
;;  `anything-dabbrev-find-all-buffers'
;;    Display dabbrev candidates in all buffers.
;;
;;; Customizable Options:
;;
;; Below are customizable option list:
;;

;;; Installation:

;; Put this file into your load-path, and add following line to .emacs.
;;
;;   (require 'anything-dabbrev-expand)
;;   (global-set-key "\M-/" 'anything-dabbrev-expand)
;;   (define-key anything-dabbrev-map "\M-/" 'anything-dabbrev-find-all-buffers)

;;; Usage:

;; anything-dabbrev-expand behaves as follows.
;;
;; (1) First, execute `anything-dabbrev-expand'.
;;     And this function behaves as well as normal dabbrev-expand.
;; (2) Next, execute `anything-dabbrev-expand' again.
;;     Then `anything' selection menu appears.
;;     It contains dabbrev candidates in current buffer (partial match).
;; (3) After waiting for `anything-dabbrev-idle-delay' seconds in selection menu,
;;     It searches dabbrev candidates from all buffers.
;;
;;     or
;; (3')execute `anything-dabbrev-find-all-buffers' in selection menu.
;;     It searches dabbrev candidates from all buffers.

;;; Note:

;; The main idea of this package is based on dabbrev-expand-multiple.el.
;; dabbrev-expand-multiple.el has Copyright to khiker.

;; This package requires Ruby interpreter. <URL:http://www.ruby-lang.org/>

;;; Customize:

;; You can customize `anything-dabbrev-expand' strategy.
;; See `anything-dabbrev-expand-strategies' docstring.
;; [EVAL IT] (describe-variable 'anything-dabbrev-expand-strategies)

;;; History:

;; $Log: anything-dabbrev-expand.el,v $
;; Revision 1.20  2009/04/20 16:26:43  rubikitch
;; Set anything-samewindow to nil
;;
;; Revision 1.19  2009/04/18 10:10:53  rubikitch
;; * auto-document.
;; * Use anything-show-completion.el if available.
;;
;; Revision 1.18  2008/09/22 09:17:03  rubikitch
;; *** empty log message ***
;;
;; Revision 1.17  2008/08/28 13:02:11  rubikitch
;; `anything-dabbrev-expand--first-partial-dabbrev': allow prefix match too
;;
;; Revision 1.16  2008/08/28 10:06:36  rubikitch
;; `anything-dabbrev-make-candidates--partial-match': arranged candidate order
;;
;; Revision 1.15  2008/08/26 11:03:57  rubikitch
;; `anything-dabbrev-make-candidates--partial-match': remove pattern itself
;;
;; Revision 1.14  2008/08/26 10:56:58  rubikitch
;; change defalut values.
;; Use cancel-timer.
;;
;; Revision 1.13  2008/08/26 02:51:57  rubikitch
;; *** empty log message ***
;;
;; Revision 1.12  2008/08/25 12:02:23  rubikitch
;; `anything-dabbrev-partial-source':
;;   use candidates-in-buffer
;;   show closer candidates first
;; `anything-dabbrev-expand--first-dabbrev': search current buffer only for speed
;;
;; Revision 1.11  2008/08/12 15:43:31  rubikitch
;; Use `anything--dabbrev-char-regexp' instead of `dabbrev--abbrev-char-regexp',
;; because Ruby cannot parse some Emacs' regexp meta characters.
;;
;; Revision 1.10  2008/07/01 11:58:43  rubikitch
;; restore target string when quitting anything.
;;
;; Revision 1.9  2008/07/01 10:48:55  rubikitch
;; first dabbrev => first partial dabbrev => anything
;;
;; Revision 1.8  2008/06/30 16:43:27  rubikitch
;; update doc
;;
;; Revision 1.7  2008/06/30 16:41:16  rubikitch
;; partial match support
;;
;; Revision 1.6  2008/03/21 02:11:28  rubikitch
;; bugfix: avoid colecting candidates from all buffers when anything is exited.
;; New variable: anything-dabbrev-all-min-length
;;
;; Revision 1.5  2008/01/27 15:17:33  rubikitch
;; automatically search dabbrev candidates from all buffers.
;;
;; Revision 1.4  2008/01/14 04:19:31  rubikitch
;; supress compilation warning
;;
;; Revision 1.3  2008/01/14 04:08:45  rubikitch
;; small bugfix
;;
;; Revision 1.2  2008/01/14 04:04:41  rubikitch
;; * added `require'.
;; * revive `target' when quitting `anything'.
;;
;; Revision 1.1  2008/01/13 20:58:57  rubikitch
;; Initial revision
;;

;;; Code:

(require 'dabbrev)
(require 'anything)

(when (require 'anything-show-completion nil t)
  (use-anything-show-completion 'anything-dabbrev-expand
                                '(length anything-dabbrev-last-target)))

(defvar anything-dabbrev-map (copy-keymap anything-map)
  "Keymap for `anything-dabbrev-expand'. It is based on `anything-map'.")
(defvar anything-dabbrev-idle-delay 0.7
  "*The user has to be idle for this many seconds, before
  dabbrev candidates from all buffers are collected.")
(defvar anything-dabbrev-input-idle-delay anything-input-idle-delay)
(defvar anything-dabbrev-all-min-length 4
  "*Automatically collects candidates from all buffers when input is larger than this value.")
(defvar anything--dabbrev-char-regexp "[a-zA-Z0-9?!_-]"
  "Regexp of characters of dabbrev candidates. It is parsable by Ruby and Emacs.")

(defvar anything-dabbrev-last-target nil)
(defvar anything-dabbrev-expand-candidate-number-limit 15
  "*Do not show more candidates than this limit from dabbrev candidates.")
(defvar anything-dabbrev-candidates nil)
(defvar anything-dabbrev-partial-candidates nil)
(defvar anything-dabbrev-all-candidates nil)
(defvar anything-dabbrev-candidate-inserted nil)
(defvar anything-dabbrev-source
  '((name . "dabbrev")
    (init
     . (lambda ()
         (setq anything-dabbrev-candidates (anything-dabbrev-get-candidates abbrev))))
    (candidates . anything-dabbrev-candidates)
    (action . anything-dabbrev-insert-candidate)
    (volatile)))
(defvar anything-dabbrev-partial-source
  '((name . "dabbrev (partial match)")
    ;;(candidates . anything-dabbrev-partial-candidates)
    (init . anything-dabbrev-make-candidates--partial-match)
    (candidates-in-buffer)
    (action . anything-dabbrev-insert-candidate)))

(defvar anything-dabbrev-all-source-timer nil)
(defvar anything-dabbrev-all-source
  '((name . "dabbrev (all buffer)")
    (init
     . (lambda ()
         (setq anything-dabbrev-all-candidates nil)
         (setq anything-dabbrev-all-source-timer
               (run-with-idle-timer
                anything-dabbrev-idle-delay nil
                (lambda ()
                  (when (and (get-buffer-window anything-buffer)
                             (>= (length anything-dabbrev-last-target) anything-dabbrev-all-min-length))
                    (setq anything-dabbrev-all-candidates
                          (anything-dabbrev-get-all-candidates anything-dabbrev-last-target))
                    (anything-update)))))))
    (cleanup . (lambda () (cancel-timer anything-dabbrev-all-source-timer)))
    (candidates . anything-dabbrev-all-candidates)
    (action . anything-dabbrev-insert-candidate)
    (volatile)))
(defvar anything-dabbrev-sources
  '(anything-dabbrev-partial-source anything-dabbrev-all-source))

(defun anything-dabbrev-insert-candidate (c)
  (delete-backward-char (length anything-dabbrev-last-target))
  (insert c)
  (setq anything-dabbrev-candidate-inserted t))

;; dabbrev strategies
(defvar anything-dabbrev-expand-strategies
  '(anything-dabbrev-expand--first-dabbrev
    anything-dabbrev-expand--first-partial-dabbrev
    anything-dabbrev-expand--anything)
  "Strategy of `anything-dabbrev-expand'.
If you prefer normal dabbrev, eval this sexp:
  (setq anything-dabbrev-expand-strategies
    '(anything-dabbrev-expand--first-dabbrev
      anything-dabbrev-expand--anything))

If you only use partial dabbrev, eval this sexp:
  (setq anything-dabbrev-expand-strategies
    '(anything-dabbrev-expand--first-partial-dabbrev
      anything-dabbrev-expand--anything))
")

;; strategy function must return nil on failure.
(defun anything-dabbrev-expand--anything (target pt)
  (let ((newstr (buffer-substring pt (point))))
    (delete-region pt (point))
    (insert anything-dabbrev-last-target)
    (anything-dabbrev-expand-main target)))

(defun anything-dabbrev-expand--first-dabbrev (target pt)
  (let* ((dabbrev-search-these-buffers-only (list (current-buffer)))
         (abbrev (dabbrev--find-expansion target 0 dabbrev-case-fold-search)))
    (when abbrev
      (insert (substring abbrev (length target)))
      t)))
(defun anything-dabbrev-expand--first-partial-dabbrev (target pt)
  (let (sym)
    (when
        (save-excursion
          (goto-char pt)
          (and (re-search-backward
                (format "%s*%s%s*"
                        anything--dabbrev-char-regexp target anything--dabbrev-char-regexp)
                nil t)
               (symbol-at-point)))
      (delete-region pt (point))
      (insert (match-string 0))
      (message "Partial match")
      t)))

(defun anything-dabbrev-expand ()
  "The command does dynamic abbrev expansion for multiple selection using `anything'.

When you execute this command, it behaves as well as normal
`dabbrev-expand'. It complements only one candidate.

If that candidate is not something that you want, execute this command again.
It displays multiple selection using `anything'.

The behavior is controlled by `anything-dabbrev-expand-strategies'.
"
  (interactive)
  (dabbrev--reset-global-variables)
  (setq anything-dabbrev-candidate-inserted nil)
  (let* ((n (seq-times 'anything-dabbrev-expand
                       (length anything-dabbrev-expand-strategies)))
         (strategy (nthcdr n anything-dabbrev-expand-strategies)))
    (when (zerop n)
      (setq anything-dabbrev-last-target (dabbrev--abbrev-at-point)))
    (run-hook-with-args-until-success
     'strategy anything-dabbrev-last-target
     (- seq-start-point (length anything-dabbrev-last-target)))))

(defun anything-dabbrev-get-candidates (abbrev &optional all)
  (let ((dabbrev-check-other-buffers all))
    (dabbrev--reset-global-variables)
    (dabbrev--find-all-expansions abbrev nil)))

(defun* anything-dabbrev-get-all-candidates (&optional (abbrev anything-dabbrev-last-target))
  (anything-dabbrev-get-candidates abbrev t))

(defun anything-dabbrev-make-candidates--partial-match (&optional pattern)
  "Collect all words matching pattern in the current buffer.
It uses ruby because elisp is too slow."
  (let ((buf (if (active-minibuffer-window)
                 (window-buffer (minibuffer-selected-window))
               (current-buffer))))
    (with-current-buffer buf
      (let ((wstart (window-start))
            (wend (window-end))
            (pt (point))
            (pmin (point-min))
            (pmax (point-max)))
        (setq pattern (or pattern anything-dabbrev-last-target))
        (anything-candidate-buffer 'global)
        (with-temp-buffer
          ;; In most cases, wanted partial dabbrev candidate is in visible window.
          (insert-buffer-substring buf wstart pt) (insert "\0")
          (insert-buffer-substring buf pt wend) (insert "\0")
          (insert-buffer-substring buf pmin wstart) (insert "\0")
          (insert-buffer-substring buf wend pmax)
          (call-process-region
           (point-min) (point-max) "ruby" nil (anything-candidate-buffer) nil
           "-e"
           (format
            "def g(s) (s||'').scan(%%r%s%s*%s%s*%s); end
             a=ARGF.read.split(/\\0/);
             (g(a[0]).reverse.concat(g(a[1])).concat(g(a[2]).reverse).
                concat(g(a[3])).uniq - %%w%s%s%s).each{|x| puts(x)}"
            "\001" anything--dabbrev-char-regexp pattern anything--dabbrev-char-regexp "\001"
            ;; remove pattern itself
            "\001" pattern "\001")))))))

(defun anything-dabbrev-expand-main (abbrev)
  "Execute `anything' for dabbrev candidates in current buffer."
  (let ((anything-candidate-number-limit anything-dabbrev-expand-candidate-number-limit)
        (anything-input-idle-delay anything-dabbrev-input-idle-delay)
        (anything-idle-delay anything-dabbrev-idle-delay)
        (anything-sources anything-dabbrev-sources))
    (let ((anything-map anything-dabbrev-map)
          anything-samewindow)
      (anything nil nil nil nil nil "*anything dabbrev*"))))

(defun anything-dabbrev-find-all-buffers (&rest ignore)
  "Display dabbrev candidates in all buffers."
  (interactive)
  (setq anything-dabbrev-all-candidates
        (anything-dabbrev-get-all-candidates anything-dabbrev-last-target))
  (anything-update))

;;; from EmacsWiki (oddmuse-edit "EmacsWiki" "RepeatKeyDifferentBehaviors")
(unless (fboundp 'seq-times)
  (defvar seq-store-times 0)
  (defvar seq-start-point 0
    "Stores location of pointer when sequence of calls of the same
 function was started. This variable is updated by `seq-times'")

  (defun seq-times (name &optional max)
    "Returns number of times command `name' was executed. If `max'
 is specified the counter will wrap around at the value of `max'
 never reaching it. It also updates `seq-start-point'."
    (if (eq last-command name)
        (if (= (setq seq-store-times (1+ seq-store-times)) max)
            (setq seq-store-times 0) seq-store-times)
      (setq seq-start-point (point) seq-store-times 0))))

(provide 'anything-dabbrev-expand)

;; How to save (DO NOT REMOVE!!)
;; (emacswiki-post "anything-dabbrev-expand.el")
;;; anything-dabbrev-expand.el ends here

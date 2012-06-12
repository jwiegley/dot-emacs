;;; gnus-hardsort.el -- permanently sort group by date

;;;; License
;;
;;     This file is NOT (yet) part of GNU Emacs.
;;
;;     Copyright (C) 2005  Craig McDaniel
;;
;;     This program is free software; you can redistribute it and/or
;;     modify it under the terms of the GNU General Public License as
;;     published by the Free Software Foundation; either version 2 of
;;     the License, or (at your option) any later version.
;;
;;     This program is distributed in the hope that it will be useful,
;;     but WITHOUT ANY WARRANTY; without even the implied warranty of
;;     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;;     GNU General Public License for more details.
;;
;;     You should have received a copy of the GNU General Public
;;     License along with this program; if not, write to the Free
;;     Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;;     MA 02111-1307, USA.
;; 
;;;; Commentary
;; 
;; If you prefer to view articles sorted by date, you may be annoyed
;; that articles moved from another group will appear after the
;; previously existing articles, even if the moved articles are
;; older. You can always sort your view of the articles by date, but
;; that may take a significant amount of time if there are a large
;; number of articles in the group. In addition, your default view
;; when you enter the summary buffer next time will continue to show
;; the moved articles out of order. This function permanently resorts
;; the articles in the group by date, by first sorting the articles,
;; then respooling the articles back into the same group.
;;
;;;; Usage
;; 
;; From the *Group* buffer, M-x gnus-topic-hardsort will permanently
;; resort the articles by date. When on a topic line, all groups
;; within the topic are resorted. When not on a topic line, the
;; current group is resorted or the next n groups are resorted if a
;; numeric argument is specified.

(defun gnus-group-hardsort-1 (group)
  (let* ((active (or gnus-newsgroup-active (gnus-active group)))
	 (entry (gnus-gethash group gnus-newsrc-hashtb))
	 (info (nth 2 entry)))
    (if (or (not info) (not active))
	;; There is no info on this group if it was, in fact,
	;; killed.  Gnus stores no information on killed groups, so
	;; there's nothing to be done.
	nil
      (save-excursion
        (gnus-summary-read-group group t t)
        (let ((save-split-methods nnmail-split-methods)
              (save-gnus-show-threads gnus-show-threads))
          (unwind-protect
              (progn
                (setq gnus-show-threads nil)
                (gnus-summary-sort-by-date) 
                (setq nnmail-split-methods 
                      `((,(nth 1 (split-string gnus-newsgroup-name ":")) "")))
                (gnus-summary-respool-article #x7ffffff (gnus-find-method-for-group 
                                                         gnus-newsgroup-name)))
            (setq nnmail-split-methods save-split-methods)
            (setq gnus-show-threads save-gnus-show-threads))
          (gnus-summary-exit)))
      t)))

(defun gnus-group-hardsort (group)
  (cond ((eq 'nnvirtual (car (gnus-find-method-for-group group)))
         (gnus-message 2 "Can't respool virtual group %s" 
                       (gnus-group-decoded-name group))
         nil)
        ((>= (gnus-group-level group) gnus-level-zombie)
         (gnus-message 2 "Can't respool dead group %s"
                       (gnus-group-decoded-name group))
         nil)
        (t 
         (gnus-group-goto-group group)
         (gnus-group-hardsort-1 group))))

(defun gnus-group-hardsort-current (&optional n)
  "Permanently resort the current group by date. If prefix
argument N is numeric, the next N newsgroups will be permanently
resorted.  The number of newsgroups that this function was unable
to datesort is returned."
  (interactive "P")
  (let ((groups (gnus-group-process-prefix n))
	(ret 0)
	group)
    (unless groups (error "No groups selected"))
    (if (not
	 (or gnus-expert-user
	     (gnus-y-or-n-p
	      (format
               "Do you really want to permanently resort %s? "
	       (if (= (length groups) 1)
		   (gnus-group-decoded-name (car groups))
		 (format "these %d groups" (length groups)))))))
	n
      (while (setq group (pop groups))
        (gnus-group-remove-mark group)
        (if (gnus-group-hardsort group)
            (gnus-group-update-group-line)
          (setq ret (1+ ret))))
      (gnus-group-next-unread-group 1)
      ret)))
        
(defun gnus-topic-hardsort (topic)
  "Permanently resort the groups in date-sorted order"
  (interactive (list (gnus-group-topic-name)))
  (if (not topic)
      (call-interactively 'gnus-group-hardsort-current)
    (save-excursion
      (let* ((groups
	     (mapcar (lambda (entry) (car (nth 2 entry)))
		     (gnus-topic-find-groups topic gnus-level-killed t
					     nil t)))
	     (buffer-read-only nil)
	     (gnus-group-marked groups))
	(gnus-group-hardsort-current)
	(mapcar 'gnus-topic-update-topics-containing-group groups)))))

(provide 'gnus-hardsort)

;;; end of gnus-hardsort.el

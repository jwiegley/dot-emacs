;; proof-depends.el  Functions
;;
;; Copyright (C) 2000 University of Edinburgh. 
;; Author:      Fiona McNeill
;;
;; Status:      Experimental code, currently dormant
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;; 
;; This file contains code written by Fiona McNeill for
;; her MSc project on analysing dependencies within proofs.
;; The code is currently experimental, rather Isabelle specific,
;; and not integrated with the rest of PG.
;;
;; FIXME:
;;
;; * Clean up, rationalize and integrate
;; * All functions should be renamed to proof-depends-<blah>
;;


;;The two variables below are initially set to nil then updated
;;incrementally everytime the dependency information for a span is
;;returned.  These are designed to deal with more than one file at a
;;time.  Note; only definitions that have some dependents in the file
;;are added to the list - otherwise their names are not needed.

(defvar proof-thm-names-of-files nil)
;;of form: ((file-name-1 (thm1 thm2 thm3)) (file-name-2 (thm1 thm2 thm3)))

(defvar proof-def-names-of-files nil)
;;of form: ((file-name-1 (def1 def2 def3)) (file-name-2 (def1 def2 def3)))







;;*****************************************************************************
;;DEPENDENCY INFORMATION


;;The following functions are responsible for updated the dependencies
;;and dependents information for each span and updating the two
;;variables above.

;;dependencies-within-file-list is called in proof-script.el within
;;the function proof-done-advancing.  This function is called every
;;time a span is completed.  It will set the result of
;;dependencies-within-file-list to the span-property
;;dependencies-within-file which can then be called.
;;dependencies-within-file-list takes the list of dependencies
;;returned by Isabelle and filters them to return only those
;;dependencies that are in the same file as the span.

(defun dependencies-within-file-list (dependency-list-of-strings buffer-file-name-sans-extension)
  "Takes a list of dependencies and returns those contained in buffer"
  (remove-duplicates
   (remove-nils
    (mapcar #'(lambda (theorem)
		(let ((theorem-pair (divide-string theorem)))
		  (if (equal (car theorem-pair) buffer-file-name-sans-extension)
		      (cadr theorem-pair))))
	    proof-last-theorem-dependencies))))


;;update-dependents is also called in proof-done-advancing and is
;;passed the result of dependencies-within-file-list.  This function
;;will recurse over this list and for each element will check if it is
;;a span.  Depending on this, the function then calls either
;;update-depts-thy or update-depts-ml which both add SPAN-NAME to the
;;dependents list of the first element of the list, which is classed
;;as either a span or a definition.  They then update the relevant
;;variable (see above).

;;Note: this is not ideal as there are some objects, such as ml
;;commands like [Addsimps] which are neither spans nor definitions.
;;These are classed as definitions as they fail the span test but
;;ideally they should be filtered out.


(defun update-dependents (depcs-list file file-name span-name)
  "Takes a list of dependencies and uses these to update span dependents info
For each element of depcs-list in file, span-name is added to its list of dependents"
  (while depcs-list
    (let* ((this-span-name (car depcs-list))
	   (this-span (find-span-with-prop 'name this-span-name file)))
      (if (null this-span)
	  (let ((def-name (car (split-string this-span-name "\\."))))
	       (update-depts-thy file file-name def-name span-name))
	     (update-depts-ML file this-span span-name)))
    (setq depcs-list (cdr depcs-list)))
  t)


(defun update-depts-thy (file file-name def-name span-name)
  (let* ((theory-file (concat file-name ".thy"))
	 (thy-span (find-first-span theory-file))
	 (def-list-name (intern (concat "dependents_" def-name)))
	 (new-depts-list (cons span-name (span-property thy-span def-list-name))))
    (set-span-property thy-span def-list-name new-depts-list))
  (setq proof-def-names-of-files (merge-names-list-it def-name file proof-def-names-of-files)))




	
(defun update-depts-ML (file this-span span-name)
  (let ((new-deps-list (cons span-name (span-property this-span 'dependents-within-file))))
    (set-span-property this-span 'dependents-within-file new-deps-list))
  (setq proof-thm-names-of-files (merge-names-list-it span-name file-name proof-thm-names-of-files)))




;;merge-list-name-it is an iterative function that is used to add the
;;name of the span or definition (above) and its file to the relevant
;;variable (see above).  It checks whether that name is already in the
;;list for that file and if not adds it.  If the file is not present
;;then a new list is created for this file.




(defun merge-names-list-it (name-to-add file-name list-so-far)
  "Takes the name of a span in file FILE-NAME and updates list-so-far.
This is done by locating FILE-NAME in list-so-far and adding NAME-TO-ADD to its list of span names.  If it is not in list-so-far then it is now added."
  (let ((merge-names-list '())
	(found-it nil))
    (while list-so-far
      (setq merge-names-list
	    (if (equal file-name (caar list-so-far))
		(and (setq found-it t)
		     (if (not (check-dups name-to-add (cadar list-so-far)))
			 (append (list (cons file-name (list (cons name-to-add (cadar list-so-far))))) (cdr list-so-far))
		       list-so-far))
	      (append (list (car list-so-far)) merge-names-list))
	    list-so-far (cdr list-so-far)))
    (if found-it
	merge-names-list
      (append (list (list file-name (list name-to-add))) merge-names-list))))






  



;;*****************************************************************************
;;MENU FUNCTIONS

;;The following functions set up the menus which are the key way in
;;which the dependency information is used.

;;There are three menus; one which appears when the user right-clicks
;;in a span, one when the user right-clicks outside a span in the ML
;;file and one when the user right-clicks in the theory file.

;;***************
;;SPAN MENUS


;;The menu below appears when the user right-clicks in a span.  This
;;is taken as an event; the event is passed to span-context-menu which
;;sets the span as event-span and calls the creation of the
;;span-context-menu.  Span-context-menu-keymap defines a keymap
;;whereby button 3 causes this menu to appear.

;;Note: there are two functions on this menu which are not defined as
;;yet; this functionality will hopefully be added soon.

(defun create-in-span-context-menu (span file)
  `("Span-menu"
    ,(make-dependents-list span file)
    ,(make-dependencies-list span file)
    "-------------"
    ,(make-highlight-depts-menu file)
    ,(make-highlight-depcs-menu file)
    ,(unhighlight-cmd file)
    "------------"))
;    ["Cycle through dependent spans" (message "need to work this out") t]
;    ["Cycle through dependence spans" (message "need to work this out") t]))

(defun span-context-menu (event)
  (interactive "e")
  (select-window (event-window event))
  (setf event-span (span-at (event-point event) 'type))
  (let ((event-file (buffer-name (span-object event-span))))
    (popup-menu (create-in-span-context-menu event-span event-file))))



(defvar span-context-menu-keymap
    (let ((map (make-sparse-keymap
		"Keymap for context-sensitive menus on spans")))
      (define-key map [button3] 'span-context-menu)
      map))



;;the following items build up list of the form ("name" ["subname" action t] ... ["subnamex" actionx t]) which is passed back to create-in-span-context-menu.  This is a way of building up the menu when not all of the informatino is known initially; this setup means `action' will only be called when that menu item is chosen and the information need not be known when the menu is set up.  "name" is typically a command such as "Move to span" and "subname" is typically the name of, in this case, a span that can be chosen to move to.  `action' must contain all the information that is needed to call the particular function without any further evaluation; for example, (unhighlight "loading.ML") is a correct possibility, (unhighlight file) is not because file is not evaluated.

;;If the list returned will be empty then each function returns just a
;;string containing the name of the command, such as "Move to span";
;;this causes it to appear in the menu as unselectable text so that
;;the user can see it is not an appropriate command.

;;make-depcs-list returns a sublist consisting of two further sublists
;;because it is convenient in this case to distinguish between spans
;;and dependencies.


(defun make-dependents-list (span file)
  "Returns a menu item submenu which gives the option to move to any dependent"
  (let ((depts-list (span-property span 'dependents-within-file)))
    (if (null depts-list)
	"Move to dependent"
      (cons "Move to dependent" (make-depts-list-it depts-list file)))))

(defun make-depts-list-it (depts-list file)
  (let ((depts-list-menu '()))
    (while depts-list
     (let ((span-with-name (find-span-with-prop 'name (car depts-list) file)))
       (setq depts-list-menu
	     (cons 
	      `[,(car depts-list) (and (goto-char ,(+ 2 (span-start span-with-name))) (recenter)) t]
	      depts-list-menu)
	      depts-list (cdr depts-list))))
    depts-list-menu))
	    



(defun make-dependencies-list (span file)
  "Returns a menu item submenu which gives the option to move to any dependence."
  (let* ((span (if (null span) (span-at (point) 'type) span))
	 (file (buffer-name (span-object span)))
	 (file-name-sans-extension (car (split-string file "\\.")))
	 (thy-file-name (concat file-name-sans-extension ".thy"))
	 (depcs-list (span-property span 'dependencies-within-file))
	 (returned-list (make-depcs-list-it depcs-list file)))
    (setf current-thy-file thy-file-name)
    (cons "Move to dependency" returned-list)))
    

(defun make-depcs-list-it (depcs-list file)
  (let ((depcs-list-menu '())
	(defs-list '())
	(span-list '()))
    (while depcs-list
      (let ((span-with-name (find-span-with-prop 'name (car depcs-list) file)))
	(if (null span-with-name)
	    (setq defs-list (cons (car depcs-list) defs-list))
	  (setq span-list (cons span-with-name span-list)))
	(setq depcs-list (cdr depcs-list))))
    (let ((defs-list-menu-items (make-depcs-defs-list-it defs-list))
	  (span-list-menu-items (make-depcs-span-list-it span-list)))
      (if (null defs-list-menu-items)
	  (if (null span-list-menu-items)
	      '("definitions" "spans")
	    (cons "definitions" (list (cons "spans" span-list-menu-items))))
	(if (null span-list-menu-items)
	    (cons (cons "definitions" defs-list-menu-items) (cons "spans" nil))
	  (append (list (cons "definitions" defs-list-menu-items)) (list (cons "spans" span-list-menu-items))))))))



(defun make-depcs-defs-list-it (defs-list)
  (let ((defs-list-menu '()))
    (while defs-list
      (setq defs-list-menu
	    (cons
	     `[,(car defs-list) (move-to-def ,(car defs-list)) t]
	     defs-list-menu)
	    defs-list (cdr defs-list)))
    defs-list-menu))


(defun make-depcs-span-list-it (span-list)
  (let ((span-list-menu '()))
    (while span-list
      (let ((current-span (car span-list)))
	(setq span-list-menu
	      (cons
	       `[,(span-property current-span 'name) (goto-char ,(+ 2 (span-start current-span))) t] 
	       span-list-menu)
	      span-list (cdr span-list))))
    span-list-menu))
	      


(defun make-highlight-depts-menu (file)
  "Return a menu item that will highlight the dependents of event-span"
  (if (null (span-property event-span 'dependents-within-file))
      "Highlight all dependent spans"
    '["Highlight all dependent spans" (highlight-depts-of-span file) t]))

(defun make-highlight-depcs-menu (file)
  "Return a menu item that will highlight the depencdencies of event-span"
  (if (null (span-property event-span 'dependencies-within-file))
	"Highlight all dependence spans"
      '["Highlight all dependence spans" (highlight-depcs-of-span file) t]))




(defun move-to-def (def)
  "Brings up the theory file and moves the cursor to the first mention of DEF."
  (save-excursion
    (set-buffer current-thy-file)
    (let ((def-name (car (split-string def "\\."))))
      (and (find-file-other-window current-thy-file)
	   (goto-char (- (search-forward def-name) (length def-name)))))))
    


(defun unhighlight-cmd (file)
  `["Unhighlight" (unhighlight ,file) t])











;;**********************
;;ML-FILE MENU


;;The following functions define the menu that appears in the ml file
;;outwith a span.

;;Since there is already a menu defined here that we wish to add to
;;rather than replace, it is not necessary to set up the event as
;;above.  Rather, we simply indicate that proof-menu-define-deps
;;belongs to proof-mode-map.  Everytime the function
;;proof-done-advancing in proof-script.el (see above) is called, the
;;span information gets updated and we wish to re-evaluate this menu.
;;This is because this menu contains items such as move to spans,
;;where we require an up to date list of all spans.  Since we wish
;;this menu to be available at any point rather than just at the end
;;this process is done incrementally.

;;So everytime proof-done-advancing is called, proof-deps-menu (the
;;name of the menu created by proof-menu-define-deps) is removed from
;;proof-mode-map, if it exists, and once the span working has been
;;done proof-menu-define-deps is re-evaluted and the new value is then
;;added to proof-deps-menu.  All this is done in proof-script.el.


(defun proof-menu-define-deps (file)
  (easy-menu-define 
   proof-deps-menu  
   proof-mode-map
   "The dependency menu"
   `("Dependence info"
     ,(highlight-depts-spans file)
     ,(highlight-depcs-spans file)
     ,(highlight-depts-defs file)
     ,(unhighlight-cmd file)
     "--------------"
     ,(move-to-spans file)
     ,(goto-thy-file file))))


;;The following functions returns submenus of the form described
;;above.  The particular action that these menu items do should be
;;obvious from the function name, for example highlight-depts-spans
;;returns a submenu which appears to user as follows: the name
;;"Highlight dependents of span" appears in the menu, if this is
;;chosen then the option of all choosing any span appears, when a span
;;is chosen its dependents are highlighted.



(defun highlight-depts-spans (file)
  "Returns a menu item which is either a string or a submenu.
If the current event-span has no dependents then the menu name is given as unselectable text.  Otherwise a submenu is returned, each item containing the name of a span and the direction to highlight its dependents."
  (let ((thm-names-list (find-thm-or-def-list-it proof-thm-names-of-files file)))
    (if (null thm-names-list)
	"Highlight dependents of span"
      (cons "Highlight dependents of span" (highlight-depts-spans-it thm-names-list file)))))
  



(defun highlight-depts-spans-it (thm-names-list file)
  (let ((menu-list '()))
    (while thm-names-list
      (setq menu-list
	    (cons
	     `[,(car thm-names-list) (highlight-depts-of-span-name ,(car thm-names-list) ,file) t] 
	     menu-list)
	    thm-names-list (cdr thm-names-list)))
    menu-list))



(defun highlight-depcs-spans (file)
   "Returns a menu item which is either a string or a submenu.
If the current event-span has no dependencies then the menu name is given as unselectable text.  Otherwise a submenu is returned, each item containing the name of a span and the direction to highlight its dependencies."
   (let ((thm-names-list (find-thm-or-def-list-it proof-thm-names-of-files file)))
      (if (null thm-names-list)
	  "Highlight dependencies of span"
	(cons "Highlight dependencies of span" (highlight-depcs-spans-it thm-names-list file)))))
  



(defun highlight-depcs-spans-it (thm-names-list file)
  (let ((menu-list '()))
    (while thm-names-list
      (setq menu-list
	    (cons
	     `[,(car thm-names-list) (highlight-depcs-of-span-name ,(car thm-names-list) ,file) t] 
	     menu-list)
	    thm-names-list (cdr thm-names-list)))
    menu-list))



(defun find-thm-or-def-list-it (list file)
  "Returns a list of all the thm or def names in file.
LIST is a variable containing list of two elements: the first being the file name and the second being a list of thm / def names.  If FILE matches any of these file names then the associated list is returned."
  (let ((right-list '()))
    (while list
      (if (equal file (caar list))
	  (setq right-list (cadar list)))
      (setq list (cdr list)))
    right-list))


(defun move-to-spans (file)
  "Returns a menu item which is either unselectable text or a submenu.
A list of menu items containing thm names and a command to move to them is returned."
    (let ((thm-names-list (find-thm-or-def-list-it proof-thm-names-of-files file)))
      (if (null thm-names-list)
	  "Move to span"
	(cons "Move to span" (move-to-spans-it thm-names-list file)))))

(defun move-to-spans-it (thm-names-list file)
  (let ((menu-list '()))
    (while thm-names-list
      (setq menu-list
	    (cons
	     `[,(car thm-names-list) (and (move-to-span-name ,(car thm-names-list) ,file) (recenter)) t]  
	     menu-list)
	    thm-names-list (cdr thm-names-list)))
    menu-list))



(defun move-to-span-name (span-name file)
  (goto-char (+ 2 (span-start (find-span-with-prop 'name span-name file)))))




(defun goto-thy-file (file)
  "Opens the theory file connected to the ml-file FILE"
  (let ((thy-file (concat (car (split-string file "\\.")) ".thy")))
    `["Move to thy file" (find-file ,thy-file) t]))




;;**********************
;;THY-FILE MENU


;;The following functions define the menu that appears in the theory file.

;;This is added to the theory menu in thy-mode.el and then updated in
;;proof-script.el, as above, which rather than calling
;;thy-menu-define-deps and adding that to the menu, in fact calls
;;thy-added-menu in which the commands to remove, update and add this
;;to the thy-menu are.  Hence it is tied in to the existing theory
;;menu.


(defun thy-menu-define-deps (file)
  (easy-menu-define 
   thy-mode-deps-menu  
   thy-mode-map
   "The dependency menu"
   `("Dependence info"
     ,(highlight-depts-defs file)
     ,(unhighlight-cmd file)
     "-------------"
     ,(move-to-spans-from-thy-file file)
     ,(goto-ml-file file))))


;;The functions below are evaluated in a similar manner to above.



  
(defun goto-ml-file (file)
    `["Move to ml file" (find-file ,file) t])


   

(defun highlight-depts-defs (file)
  "Highlights the dependents of a definition."
    (let ((def-names-list (find-thm-or-def-list-it proof-def-names-of-files file)))
      (if (null def-names-list)
	  "Highlight dependents of definition"
	(cons "Highlight dependents of definition" 
	      (highlight-depts-defs-it def-names-list file)))))



(defun highlight-depts-defs-it (def-names-list file)
  (let ((answer '()))
    (while def-names-list
      (setq answer
	    (cons
	     `[,(car def-names-list) (highlight-depts-of-def ,(car def-names-list) ,file) t]
	     answer)
	    def-names-list (cdr def-names-list)))
    answer))


(defun move-to-spans-from-thy-file (file)
  "Returns a menu item which is a submenu or unselectable text.
A submenu is returned whose elements are the names of the theorems and instructions to move to that text in FILE"
    (let ((thm-names-list (find-thm-or-def-list-it proof-thm-names-of-files file)))
      (if (null thm-names-list)
	  "Move to span"
	(cons "Move to span" (move-to-spans-from-thy-it thm-names-list file)))))




(defun move-to-spans-from-thy-it (thm-names-list file)
  (let ((menu-list '()))
    (while thm-names-list
      (setq menu-list
	    (cons
	     `[,(car thm-names-list) (and (move-to-span-from-thy-name ,(car thm-names-list) ,file) (recenter)) t]
	     menu-list)
	    thm-names-list (cdr thm-names-list)))
    menu-list))



(defun move-to-span-from-thy-name (span-name file)
    (and (find-file file)
	 (goto-char (+ 2 (span-start (find-span-with-prop 'name span-name file))))))










;;***************************************************************************
;;HIGHLIGHTING FUNCTIONS


;;The following functions are responsible for actually highlighting
;;the data and are called by the functions in the menu section when
;;they are setting up the submenus.

;;They work by immediately unhighlighting all highlighting that exists
;;at present and then working through a given list of spans setting
;;the span's face property to the appropriate colour.  These colours
;;are defined in proof-config.el.  The given list is calculated from
;;dependents/dependency information.


;;Some of the functions are passed only a file and calculate
;;information using the event file; these are those that are called
;;from the span-context menu and hence a current event-span is set.
;;Others are passed a particular span or span-name; these are called
;;from the ml and thy menus when there is no event-span and
;;information can be returned about any span.

;;In most cases these functions will merely highlighting the
;;appropriate spans and return nothing; the exception is
;;highlight-depcs-of-span-it.  This is unusual in that it is called
;;when there is sometimes no highlighting to be done.  Dependency
;;information contains both spans and defintions, but highlighting is
;;inappropriate for a definition because it would merely mean
;;highlighting the whole of the theory file; the theory file is not
;;divided into spans.  Therefore a message is returned to explain to
;;the user why no dependency information is highlighted even there
;;dependencies within the file exist.



(defun highlight-depts-of-span (file)
  "Finds all the dependents of the current event-span and highlights them"
  (unhighlight file)
  (let ((depts-list (span-property event-span 'dependents-within-file)))
    (highlight-depts-of-span-it depts-list file)))




(defun highlight-depts-of-span-name (span-name file)
  "Finds all the dependents of span with name SPAN-NAME and highlights them"
  (let ((span (find-span-with-prop 'name span-name file)))
    (unhighlight file)
    (let ((depts-list (span-property span 'dependents-within-file)))
      (highlight-depts-of-span-it depts-list file))))





(defun highlight-depts-of-span-it (depts-list file)
  (while depts-list
    (let ((next-depts-span (find-span-with-prop 'name (car depts-list) file)))
      (set-span-property next-depts-span 'face 'proof-highlight-dependent-face))
    (setq depts-list (cdr depts-list))))







(defun highlight-depts-of-def (def-name file)
  "Highlights all the dependents of the definition named DEF-NAME"
  (unhighlight file)
  (find-file file)
  (let ((thy-file (concat (car (split-string file "\\.")) ".thy")))
    (save-excursion
      (set-buffer thy-file)
      (let* ((thy-span (span-at (point-min) 'type))
	     (depts-list-name (intern (concat "dependents_" def-name)))
	     (depts-list (span-property thy-span depts-list-name)))
	(highlight-depts-of-def-it depts-list ml-file)))))
  




(defun highlight-depts-of-def-it (depts-list file)
  (save-excursion
    (set-buffer file)
    (while depts-list
      (let ((next-depts-span (find-span-with-prop 'name (car depts-list) file)))
      (set-span-property next-depts-span 'face 'proof-highlight-dependent-face))
      (setq depts-list (cdr depts-list)))))






(defun highlight-depcs-of-span (file)
  "Highlights all dependencies of event-span"
  (unhighlight file)
  (let ((depcs-list (span-property event-span 'dependencies-within-file)))
    (highlight-depcs-of-span-it depcs-list file)))



(defun highlight-depcs-of-span-name (span-name file)
  "Highlights all dependencies of span with name SPAN-NAME"
  (let ((span (find-span-with-prop 'name span-name file)))
    (unhighlight file)
    (let ((depcs-list (span-property span 'dependencies-within-file)))
	(highlight-depcs-of-span-it depcs-list file))))




(defun highlight-depcs-of-span-it (depcs-list file)
  (let ((exists-some-depc-span nil))
    (while depcs-list
      (let ((next-depcs-span (find-span-with-prop 'name (car depcs-list) file)))
	(if next-depcs-span 
	    (and (set-span-property next-depcs-span 'face 'proof-highlight-dependency-face)
		 (setq exists-some-depc-span t)))
	(setq depcs-list (cdr depcs-list))))
    (if (not exists-some-depc-span)
	(and (message "This span has dependence on definition(s) but not on other spans in this file")
	       (ding)))))


(defun unhighlight (file)
  "Returned all highlighted spans in file to the proof-locked-face highlighting"
      (save-excursion
	(set-buffer file)
	(let ((first-span (span-at (point-min) 'type)))
	  (unhighlight-it first-span)))) 


(defun unhighlight-it (span)
  (while span
    (set-span-property span 'face 'proof-locked-face)
    (setq span (next-span span 'type))))














;;*****************************************************************************
;;AUXILARY FUNCTIONS


;;The following functions do not fall into any of the above catagories and are used as tools within larger functions.  The function names should make their actions clear.


(defun find-first-span (file)
  "this function takes a file and returns the span found at point-min"
  (find-file-noselect file)
  (save-excursion
    (set-buffer file)
    (span-at (point-min) 'type)))




	      

(defun find-span-with-prop (type-prop value-prop file)
  "Returns the span in FILE that has VALUE-PROP as its value for type TYPE-PROP.
Creates a list of all the spans in FILE and checks each one.  Terminates when the first matching span in found."
  (save-excursion
    (set-buffer file)
    (let ((list-of-spans (extent-list))
	  (right-span nil))
      (while (and list-of-spans
		  (not right-span))
	(if (equal value-prop (span-property (car list-of-spans) type-prop))
	    (setq right-span (car list-of-spans)))
	(setq list-of-spans (cdr list-of-spans)))
      right-span)))
	      




(defun divide-string (string)
  "this function takes a string containing a dot and splits it into a list of two strings containing what was on each side of the dot"
  (let ((dot (string-match "\\." string)))
    (list (substring string 0 dot) (substring string (+ dot 1)))))






(defun remove-nils (list)
  (let ((returned-list '()))
    (while list
      (if (car list)
	  (setq returned-list (cons (car list) returned-list)))
      (setq list (cdr list)))
    returned-list))




(defun remove-duplicates (list)
  (let ((returned-list '()))
    (while list
      (if (not (check-dups (car list) (cdr list)))
	  (setq returned-list (cons (car list) returned-list)))
      (setq list (cdr list)))
    returned-list))
	  




(defun check-dups (element list)
  (let ((truth nil))
    (while list
      (if (equal element (car list))
	  (setq truth t))
      (setq list (cdr list)))
    truth))


(provide 'proof-depends)
;; proof-depends.el ends here

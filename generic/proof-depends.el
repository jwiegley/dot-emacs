;;here is the code to return a list of all the dependencies

;;FIXME: doesn't even slightly work.  First prob is that span-at does not return a span, only nil.  Therefore cannot test the rest of the code as just fails at this point.

(defun make-dependency-list (file)
  (make-deps-list '() (span-at (point-min file) 'dependencies) (point-max file)))
(defun make-deps-list (list span end-point)
  (if (eql (span-end span) end-point)
      (append list (span-property span 'dependencies))
   (make-deps-list (append list (span-property span 'dependencies)) (next-span span 'dependencies) end-point)))

(defun mytest ()
  (save-excursion
   (set-buffer proof-script-buffer)
   (span-at (point-min) 'type)))

(defun find-span (buffer)
  (save-excursion
    (set-buffer buffer)
    (span-at (point-min) 'type)))

(span-property (find-span "loading.ML") 'type)



(find-span "loading.ML")

(defun find-next-span (buffer span)
  (save-excursion
    (set-buffer buffer)
    (next-span span 'type)))

(span-property (find-next-span "loading.ML" (find-span "loading.ML")) 'dependencies)




;; this is code to add dependency info to files not read through the interface.

;;some testing for matching stuff

So ... one idea is: find out where the message starts, move on x nos of steps from there and then return everything between that place and where we find val it = ().

So ... what buffer is this in?   - response buffer

(let ((proof-last-theorem-dependencies 
(string-match proof-shell-theorem-dependency-list-regexp message)

(setq p-s-t-d-l-r "Proof General, the theorem dependencies are: ")

(goto-char (+ 45 (string-match p-s-t-d-l-r messq)) (get-buffer "empty"))
;;this returns 60
(search-forward "val it" nil nil nil (get-buffer "empty"))
;;this returns 217

;;so we know that all the information we want is contained in the buffer "empty" between lines 61 and 217.

(car (setq lala (read-from-string "blah blah blah Proof General, the theorem dependencies are: (ProtoPure.rev_triv_goal Protopure.triv_goal HOL.TrueI ProtoPure.rev_triv_goal ProtoPure.triv_goal ProtoPure.revcut_rl HOL.subst loading.even_Suc_Suc) 
val it = () : unit

this is a file with lots of stuff in it so that I can practice
searching and see what happens 

lots of fun la di la" 60)))

(read-from-string "A short string" 0 10)

(setq noodle (buffer-string (point-min "*isabelle*") (point-max "*isabelle*") (get-buffer "*isabelle*")))

(read-from-string noodle (goto-char (+ 45 (string-match p-s-t-d-l-r noodle)) "*isabelle*"))

(get-buffer "*isabelle*")


(save-excursion
  (set-buffer "*isabelle*")
  (end-of-buffer)
  (search-backward p-s-t-d-l-r)
  (setq beginning (+ 47 (point)))
  (search-forward "val it")
  (buffer-string beginning (- (point) 10)))


(setq messq "blah blah blah Proof General, the theorem dependencies are: ProtoPure.rev_triv_goal ProtoPure.triv_goal HOL.TrueI ProtoPure.rev_triv_goal ProtoPure.triv_goal ProtoPure.revcut_rl HOL.subst loading.even_Suc_Suc 
val it = () : unit")













;;sort-deps-list will sort through the list of dependencies and return all those that are not either Protopure or HOL - i.e. will return only those theorems that are written within the file and subject to alteration

;;FIXME: check that ProtoPure and HOL are the only cases that need to be checked for.

(defun sort-deps-list (list1)
  (if (null list1)
      nil
    (if (or (string= '"ProtoPure" (substring (prin1-to-string (car list1)) 0 9))
	    (string= '"HOL" (substring (prin1-to-string (car list1)) 0 3)))
	(sort-deps-list (cdr list1))
      (cons (car list1) (sort-deps-list (cdr list1))))))

(sort-deps-list (car lala))



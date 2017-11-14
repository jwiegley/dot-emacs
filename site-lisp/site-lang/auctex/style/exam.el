;;; exam.el --- AUCTeX style for the (LaTeX) exam class

;; Copyright (C) 2016, 2017 Free Software Foundation, Inc.

;; Author: Uwe Brauer <oub@mat.ucm.es>
;; Created: 2016-03-06
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for the exam class.

;; Acknowledgements
;; Arash Esbati <arash@gnu.org> for a almost complete rewrite.

;;; Code:

(defvar LaTeX-exam-class-options
  '("answers" "noanswers" "cancelspace" "nocancelspace" "addpoints")
  "Class options for the exam class.")

(defun LaTeX-exam-insert-item ()
  "Insert a new item in an environment from exam class.
Item inserted depends on the environment."
  (TeX-insert-macro
   (cond ((string= environment "questions")
          "question")
         ((string= environment "parts")
          "part")
         ((string= environment "subparts")
          "subpart")
         ((string= environment "subsubparts")
          "subsubpart")
         ;; Fallback
         (t "item"))))

(defun LaTeX-exam-insert-label (_optional &optional name type)
  "Indent the line and query/insert a label incl. the \"\\label\" macro.
Arguments NAME and TYPE are the same as for the function
`LaTeX-label'.  OPTIONAL is ignored."
  (indent-according-to-mode)
  (let ((currenv (LaTeX-current-environment)))
    (LaTeX-label (or name currenv) (or type 'environment))))

(TeX-add-style-hook
 "exam"
 (lambda ()
   (TeX-run-style-hooks "article")
   ;; Add options from `LaTeX-article-class-options' only once:
   (dolist (opt LaTeX-article-class-options)
     (add-to-list 'LaTeX-exam-class-options opt))
   ;; Make our label prefix available ...
   (let ((envs '("questions")))
     (dolist (env envs)
       ;; to AUCTeX
       (add-to-list 'LaTeX-label-alist
                    (cons env 'LaTeX-exam-label))
       ;; to RefTeX with `reftex-add-label-environments'
       (when (fboundp 'reftex-add-label-environments)
         (reftex-add-label-environments
          `((,env ,LaTeX-exam-reftex-quick-id-key ,LaTeX-exam-label
                  "~\\ref{%s}" nil
                  (regexp "[Qq]uestions?" "[Nn]umbers?")))))))
   (when (or (member "xcolor" (TeX-style-list))
             (member "color" (TeX-style-list)))
     (TeX-add-symbols '("shadedsolutions" 0)))

   (LaTeX-add-environments
    '("solution" [ "Height" ])
    '("select")
    '("solutionorbox" [ "Height" ])
    '("solutionorlines" [ "Height" ])
    '("solutionordottedlines" [ "Height" ])
    '("solutionorgrid" [ "Height" ])
    '("questions" LaTeX-env-item)
    '("parts" LaTeX-env-item)
    '("subparts" LaTeX-env-item)
    '("subsubparts" LaTeX-env-item))

   ;; Tell AUCTeX about special environments:
   (let ((envs '("questions" "parts" "subparts" "subsubparts")))
     (dolist (env envs)
       (add-to-list 'LaTeX-item-list
                    (cons env 'LaTeX-exam-insert-item))))

   ;; Append us only once:
   (unless (and (string-match "question" LaTeX-item-regexp)
                (string-match "subsub" LaTeX-item-regexp))
     (set (make-local-variable 'LaTeX-item-regexp)
          (concat
           LaTeX-item-regexp
           "\\|"
           "\\(titled\\)?question\\b"
           "\\|"
           "\\(sub\\|subsub\\)?part\\b"))
     (LaTeX-set-paragraph-start))

   (TeX-add-symbols
    '("part" [ "Points" ] (TeX-arg-literal " "))
    '("subpart" [ "Points" ] (TeX-arg-literal " "))
    '("gradetable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("bonusgradetable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("bonuspointtable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("partialgradetable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("partialbonusgradetable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("partialbonuspointtable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("pointtable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )
    '("partialpointtable"
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Orientation")
                     '("v" "h") ]
      [ TeX-arg-eval completing-read
                     (TeX-argument-prompt optional nil "Table index")
                     '("questions" "pages") ] )

    '("subsubpart" [ "Points" ] (TeX-arg-literal " "))
    '("question"  ["Points"] (TeX-arg-literal " "))
    '("bonusquestion"  ["Points"] (TeX-arg-literal " "))
    '("extrafootheight"  [ TeX-arg-length "Extra height 1. page footer" ]
      (TeX-arg-length "Extra height footers"))
    '("titledquestion" "Title" ["Points"] LaTeX-exam-insert-label (TeX-arg-literal " "))
    '("ContinuedQuestion" 0)
    '("CorrectChoice" 0)
    '("CorrectChoiceEmphasis" 1)
    '("IncompleteQuestion" 0)
    '("SolutionEmphasis" 1)
    '("addpoints" 0)
    '("addquestionobject" 0)
    '("answerclearance" 1)
    '("answerline"  ["Points"] (TeX-arg-literal " "))
    '("begingradingrange" 1)
    '("bhpgword" 1)
    '("bhpword" 1)
    '("bhqword" 1)
    '("bhsword" 1)
    '("bhtword" 1)
    '("bonuspart" 0)
    '("bonuspointformat" 0)
    '("bonuspointname" 1)
    '("bonuspointpoints" 2)
    '("bonuspointsinrange" 0)
    '("bonuspointsofquestion" 1)
    '("bonuspointsonpage" 0)
    '("bonusqformat" 1)
    '("bonussubpart" 0)
    '("bonussubsubpart" 0)
    '("bonustitledquestion" "Title" ["Points"] LaTeX-exam-insert-label (TeX-arg-literal " "))
    '("bonustotalformat" 0)
    '("boxedpoints" 0)
    '("bracketedpoints" 0)
    '("bvpgword" 1)
    '("bvpword" 1)
    '("bvqword" 1)
    '("bvsword" 1)
    '("bvtword" 1)
    '("cancelspace" 0)
    '("cellwidth" 1)
    '("cfoot" 1)
    '("chbpword" 1)
    '("chead" 1)
    '("checkboxchar" 1)
    '("checkboxeshook" 0)
    '("checkedchar" 1)
    '("choice" 0)
    '("choicelabel" 0)
    '("choiceshook" 0)
    '("chpgword" 1)
    '("chpword" 1)
    '("chqword" 1)
    '("chsword" 1)
    '("chsword" 1)
    '("correctchoice" 0)
    '("correctchoiceemphasis" 1)
    '("covercfoot" 3)
    '("coverchead" 3)
    '("coverextrafootheight" 3)
    '("coverextraheadheight" 3)
    '("coverfirstpagefooter" 3)
    '("coverfirstpageheader" 3)
    '("coverfooter" 3)
    '("coverheader" 3)
    '("coverlfoot" 3)
    '("coverlhead" 3)
    '("coverrfoot" 3)
    '("coverrhead" 3)
    '("coverrunningfooter" 3)
    '("coverrunningheader" 3)
    '("cvbpword" 1)
    '("cvpgword" 1)
    '("cvpword" 1)
    '("cvqword" 1)
    '("cvsword" 1)
    '("cvtword" 1)
    '("dottedlinefillheight" 1)
    '("droppoints" 0)
    '("droptotalbonuspoints" 0)
    '("droptotalpoints" 0)
    '("endgradingrange" 1)
    '("extraheadheight" 1)
    '("extrawidth" 1)
    '("fillwithdottedlines" 1)
    '("fillwithlines" 1)
    '("firstpagefooter" 1)
    '("firstpagefootrule" 0)
    '("firstpageheader" 3)
    '("firstpageheadrule" 0)
    '("footer" 3)
    '("footrule" 0)
    '("framedsolutions" 0)
    '("fullwidth" 1)
    '("gradetablestretch" 0)
    '("greeknum" 0)
    '("half" 0)
    '("hpgword" 1)
    '("hpword" 1)
    '("hqword" 1)
    '("hsword" 1)
    '("htword" 1)
    '("ifcontinuation" 0)
    '("ifincomplete" 0)
    '("iflastpage" 0)
    '("ifprintanswers" 0)
    '("lfoot" 1)
    '("lhead" 1)
    '("linefillheight" 1)
    '("linefillthickness" 1)
    '("makeemptybox" 1)
    '("marginbonuspointname" 1)
    '("marginpointname" 1)
    '("marginpointsep" 1)
    '("marksnotpoints" 0)
    '("noaddpoints" 0)
    '("nobonusqformat" 1)
    '("noboxedpoints" 0)
    '("nobracketedpoints" 0)
    '("nocancelspace" 0)
    '("nomorequestions" 0)
    '("nopointsinmargin" 0)
    '("nopointsinrightmargin" 0)
    '("noprintanswers" 0)
    '("noqformat" 1)
    '("numbonuspoints" 0)
    '("numcoverpages" 0)
    '("numpages" 0)
    '("numparts" 0)
    '("numpoints" 0)
    '("numquestions" 0)
    '("numsubparts" 0)
    '("numsubsubparts" 0)
    '("oddeven" 2)
    '("partlabel" 0)
    '("partopsep" 0)
    '("partshook" 0)
    '("pointname" 1)
    '("pointpoints" 2)
    '("pointsdroppedatright" 0)
    '("pointsinmargin" 0)
    '("pointsinrightmargin" 0)
    '("pointsofquestion" 1)
    '("pointsonpage" 1)
    '("printanswers" 0)
    '("printselectedfalse" 0)
    '("printselectedtrue" 0)
    '("qformat" 1)
    '("questionlabel" 0)
    '("questionshook" 0)
    '("rfoot" 1)
    '("rhead" 1)
    '("rightpointsmargin" 0)
    '("roman" 0)
    '("romannumeral" 0)
    '("runningfooter" 3)
    '("runningfootrule" 0)
    '("runningheader" 3)
    '("runningheadrule" 0)
    '("settabletotalbonuspoints" 1)
    '("settabletotalpoints" 1)
    '("shadedsolutions" 0)
    '("solutiontitle" 0)
    '("subpartlabel" 0)
    '("subpartshook" 0)
    '("subsubpartlabel" 0)
    '("subsubpartshook" 0)
    '("thechoice" 0)
    '("themarginpoints" 0)
    '("thepartno" 0)
    '("thequestion" 0)
    '("thequestiontitle" 0)
    '("thesubpart" 0)
    '("thesubsubpart" 0)
    '("totalbonuspoints" 0)
    '("totalformat" 0)
    '("totalnumpages" 0)
    '("totalpoints" 0)
    '("unframedsolutions" 0)
    '("uplevel" 1)
    '("usehorizontalhalf" 0)
    '("useslantedhalf" 0)
    '("vpgword" 1)
    '("vpword" 1)
    '("vqword" 1)
    '("vsword" 1)
    '("vtword" 1)
    '("thepoints" 0)
    ;; ... more stuff here
    )
   (LaTeX-add-lengths "answerlinelength" "answerskip")

   ;; Fontification
   (when (and (featurep 'font-latex)
              (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("question"        "[")
                                ("titledquestion"  "{[")
                                ("subpart"         "[")
                                ("subsubpart"      "["))
                              'textual)))
 LaTeX-dialect)

;;; exam.el ends here

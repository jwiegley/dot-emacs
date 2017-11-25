;;; company-coq-utils.el --- Parts of company-coq that do not require Proof General or Coq to run -*- lexical-binding: t -*-

;; Copyright (C) 2015, 2016  Clément Pit--Claudel
;; Author: Clément Pit--Claudel <clement.pitclaudel@live.com>
;; URL: https://github.com/cpitclaudel/company-coq
;; Keywords: convenience, languages

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
;;
;; This file includes autoloaded functions that do not require Proof General to
;; run.  See company-coq.el for information about this package.
;;

;;; History:

;;; Code:

(defconst company-coq--coq-bibtex
  "@Manual{Coq,
  Title        = {The Coq proof assistant reference manual},
  Author       = {The Coq development team},
  Note         = {Version 8.0},
  Organization = {LogiCal Project},
  Year         = {2004},
  Url          = {http://coq.inria.fr}
}")

(defconst company-coq--pg-bibtex
  "@InCollection{ProofGeneral2000,
  Title        = {Proof General: A Generic Tool for Proof Development},
  Author       = {Aspinall, David},
  Booktitle    = {Tools and Algorithms for the Construction and
               Analysis of Systems, {TACAS} 2000},
  Publisher    = {Springer Berlin Heidelberg},
  Year         = {2000},
  Editor       = {Graf, Susanne and Schwartzbach, Michael},
  Pages        = {38--43},
  Series       = {Lecture Notes in Computer Science},
  Volume       = {1785},
  Doi          = {10.1007/3-540-46419-0_3},
  ISBN         = {978-3-540-67282-1},
  Url          = {http://dx.doi.org/10.1007/3-540-46419-0_3}
}")

(defconst company-coq--self-bibtex
  "@InProceedings{CompanyCoq2016,
  Title        = {Company-Coq: Taking Proof General one step closer to a real IDE},
  Author       = {Pit-Claudel, Clément and Courtieu, Pierre},
  Booktitle    = {CoqPL'16: The Second International Workshop on Coq for PL},
  Year         = {2016},
  Month        = jan,
  Doi          = {10.5281/zenodo.44331},
  Url          = {http://dx.doi.org/10.5281/zenodo.44331}
}")

(defconst company-coq--citations
  (list company-coq--coq-bibtex
        company-coq--pg-bibtex
        company-coq--self-bibtex))

;;;###autoload
(defun company-coq-cite ()
  "Insert BibTeX entries for Coq, PG, and company-coq."
  (interactive)
  (save-excursion
    (insert (mapconcat #'identity company-coq--citations "\n\n"))))

(provide 'company-coq-utils)
;;; company-coq-utils.el ends here

;; Local Variables:
;; nameless-current-name: "company-coq"
;; End:

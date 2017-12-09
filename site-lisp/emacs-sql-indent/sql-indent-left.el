;;; sql-indent-left.el --- configuration options to indent sql -*- lexical-binding: t -*-

;; Copyright (C) 2017  Free Software Foundation, Inc

;; Filename: sql-indent-left.el
;; Description:
;; Author: pierre.techoueyres@free.fr
;; Maintainer: pierre.techoueyres@free.fr
;; Created:
;; Version: pierre.techoueyres@free.fr
;; Last-Updated:
;;           By:
;;     Update #: 0
;; URL:
;; Keywords: language sql indentation
;; Compatibility:
;;
;; Features that might be required by this library:
;;
;;   None

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Set configuration options to indent sql my way.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change log:
;;
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'sql-indent)

(defun indent-case-statement-items (syntax base-indentation)
  ;; Look for a syntax of ((block-start when) (in-block case "") ...)
  ;; or ((block-start else) (in-block case "") ...)
  (let ((outer (sqlind-outer-context syntax)))
    (if (and (eq 'in-block (sqlind-syntax-symbol outer))
             (eq 'case (sqlind-syntax-keyword outer))
             (eq 'block-start (sqlind-syntax-symbol syntax))
             (memq (sqlind-syntax-keyword syntax) '(when else)))
        (+ base-indentation sqlind-basic-offset)
      base-indentation)))

(defvar sqlind-indentation-right-offsets-alist
  `((select-column-continuation sqlind-indent-select-column
                                sqlind-adjust-operator
                                sqlind-lone-semicolon)
    (in-select-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-right-justify-logical-operator
		      sqlind-lone-semicolon)
    (in-delete-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-right-justify-logical-operator
		      sqlind-lone-semicolon)
    (in-insert-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-right-justify-logical-operator
		      sqlind-lone-semicolon)
    (in-update-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-right-justify-logical-operator
		      sqlind-lone-semicolon)
    ;; mandatory 
    (select-table-continuation sqlind-indent-select-table +
                               sqlind-lone-semicolon)
    ;; rest picked up from the original indentation offsets
    ,@sqlind-default-indentation-offsets-alist)
  "Align sql code like this :

clear columns
set linesize 2500
set trimout on trimspool on

select atc.column_name,
       atc.data_type,
       data_length,
       data_precision,
       nullable,
       data_scale,
       nvl(substr(comments, 1, 100), atc.column_name) comments
  from   all_tab_columns atc,
         all_col_comments acc
 where  atc.owner       = acc.owner
    and    atc.table_name  = acc.table_name
    and    atc.column_name = acc.column_name
    and    atc.owner       = user
    and    atc.table_name  = 'MY_TABLE'
    and    atc.column_name = p_column_name
    and    not exists (select 1
                         from   all_tab_columns atc1,
                                all_col_comments acc1
                        where  atc1.owner       = acc1.owner
                           and    atc1.table_name  = acc1.table_name
                           and    atc1.column_name = acc1.column_name
                           and    atc1.owner       = atc.owner
                           and    atc1.table_name  = atc.table_name
                           and    acc1.column_name = acc.column_name)
 ;

delete from my_table mt
 where col_1 = v_col1
   and  (   col_2 = v_col2
         or col_3 = v_col3)
   and   col_42 = '42'
 ;

update my_table
   set    col1_has_a_long_name = value1,
          col2_is_short        = value2
 where cond1 is not null
   and  (   col_2 = v_col2
         or col_3 = v_col3)
   and   col_42 = '42'
 ;

insert into xyzxx
          ( aaa, xxx, bbb, ccc,
          ddd, eee, fff, ggg,
          hhh )
select aaa,
       xxx,
       max (m.b1) as bbb,
       min (m.b1) as ccc,
       coalesce (max (n.c2), 0)  as ddd,
       coalesce (min (n.c2), 0)  as eee,
       max (m.b1) over ( partition by c2
                        order by aaa desc ) as fff,
       min (m.b1) over ( partition by c2
                        order by aaa desc ) as ggg,
       avg (n.c2) as hhh
  from  (select * from (select aaa,
                               jjj + kkk  as b1,
                               row_number () over ( partition by qqq
                                                   order by rrr,
                                                   sss ) as rn
                          from mno)
          where rn = 1) m
          inner join (select aaa,
                             nnn + ooo as c2
                        from   pqr) n
          using (aaa),
 group by aaa,
          xxx
 order by xxx desc,
          aaa asc
 ;

")

(defvar sqlind-indentation-left-offsets-alist
  `((select-clause 0)
    (insert-clause 0)
    (delete-clause 0)
    (update-clause 0)
    (case-clause-item-cont 0)
    (block-start indent-case-statement-items)
    (begin-block 0)
    (case-clause +)
    (package +)
    (package-body +)
    (nested-statement-continuation 1)
    (string-continuation 0) ;; or shoult it be a begining of line or aligned with the previous block ?
                            ;; Anyway. It's really *BAD* to continue a string accross lines.
    (select-column-continuation sqlind-indent-select-column
                                sqlind-adjust-operator
                                sqlind-lone-semicolon)
    (in-select-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-left-justify-logical-operator
                      sqlind-lone-semicolon)
    (in-delete-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-left-justify-logical-operator
                      sqlind-lone-semicolon)
    (in-insert-clause +
                      sqlind-adjust-operator
		      sqlind-left-justify-logical-operator
                      sqlind-lone-semicolon)
    (in-update-clause sqlind-lineup-to-clause-end
                      sqlind-adjust-operator
		      sqlind-left-justify-logical-operator
                      sqlind-lone-semicolon)
    (select-table-continuation + sqlind-lone-semicolon)
    ;; rest picked up from the original indentation offsets
    ,@sqlind-default-indentation-offsets-alist)
  "Align sql code like this :

clear columns
set linesize 2500
set trimout on trimspool on

select atc.column_name,
       atc.data_type,
       data_length,
       data_precision,
       nullable,
       data_scale,
       nvl(substr(comments, 1, 100), atc.column_name) comments
from   all_tab_columns atc,
       all_col_comments acc
where  atc.owner       = acc.owner
and    atc.table_name  = acc.table_name
and    atc.column_name = acc.column_name
and    atc.owner       = user
and    atc.table_name  = 'MY_TABLE'
and    atc.column_name = p_column_name
and    not exists (select 1
                   from   all_tab_columns atc1,
                          all_col_comments acc1
                   where  atc1.owner       = acc1.owner
                   and    atc1.table_name  = acc1.table_name
                   and    atc1.column_name = acc1.column_name
                   and    atc1.owner       = atc.owner
                   and    atc1.table_name  = atc.table_name
                   and    acc1.column_name = acc.column_name)
;

delete from my_table mt
where col_1 = v_col1
and  (   col_2 = v_col2
       or col_3 = v_col3)
and   col_42 = '42'
;

update my_table
set    col1_has_a_long_name = value1,
       col2_is_short        = value2
where cond1 is not null
and  (   col_2 = v_col2
       or col_3 = v_col3)
and   col_42 = '42'
;

insert into xyzxx
          ( aaa, xxx, bbb, ccc,
            ddd, eee, fff, ggg,
            hhh )
select aaa,
       xxx,
       max (m.b1) as bbb,
       min (m.b1) as ccc,
       coalesce (max (n.c2), 0)  as ddd,
       coalesce (min (n.c2), 0)  as eee,
       max (m.b1) over ( partition by c2
                         order by aaa desc ) as fff,
       min (m.b1) over ( partition by c2
                         order by aaa desc ) as ggg,
       avg (n.c2) as hhh
from  (select * from (select aaa,
                             jjj + kkk  as b1,
                             row_number () over ( partition by qqq
                                                  order by rrr,
                                                  sss ) as rn
                      from mno)
       where rn = 1) m
        inner join (select aaa,
                           nnn + ooo as c2
                    from   pqr) n
        using (aaa),
group by aaa,
         xxx
order by xxx desc,
         aaa asc
;

")

;;;###autoload
(defun sqlind-setup-style-left ()
  "Define an sql-indentation style where keywords are left aligned."
  (interactive)
  (setq sqlind-indentation-offsets-alist sqlind-indentation-left-offsets-alist))

;;;###autoload
(defun sqlind-setup-style-right ()
  "Define an sql-indentation style where keywords are right aligned."
  (interactive)
  (setq sqlind-indentation-offsets-alist sqlind-indentation-right-offsets-alist))


;;;###autoload
(defun sqlind-setup-style-default ()
  "Define an sql-indentation style where keywords are right aligned."
  (interactive)
  (setq sqlind-indentation-offsets-alist sqlind-default-indentation-offsets-alist))


(provide 'sql-indent-left)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; sql-indent-left.el ends here

;;; ebdb-i18n.el --- Internationalization support for EBDB  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>

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

;; This file contains extensions to EBDB, making it more
;; internationally aware.  It works by hijacking many of the common
;; methods for field manipulation, attaching :extra methods to them,
;; and dispatching to new methods that allow for specialization on
;; country codes, area codes, character scripts, etc.  The new method
;; names are the same as the old names, plus a "-i18n" suffix.

;; The methods in this file are only responsible for doing the
;; hijacking, and calling the i18n versions of the original methods --
;; the i18n versions themselves live in other, country-specific,
;; libraries.  If no methods have specialized on the arguments in
;; question, an error inheriting from `cl-no-method' is signalled, and
;; the hijacker methods return control to the original methods.

;; Note to self: `ebdb-string-i18n' and `ebdb-parse-i18n' signal
;; different errors when no usable method is found.  The former raises
;; `cl-no-applicable-method', which is what I expected it to do.  The
;; latter raises `cl-no-primary-method', apparently because it has an
;; :around method.  Anyway, that's why we catch `cl-no-method'.

;;; Code:

(require 'ebdb)
(require 'ebdb-i18n-basic)

(defgroup ebdb-i18n nil
  "Options for EBDB internationalization."
  :group 'ebdb)

(defcustom ebdb-i18n-ignorable-scripts '(latin)
  "A list of script types that should be considered \"standard\";
  ie, no special handling will be done for them."
  :type 'list
  :group 'ebdb-i18n)

(defcustom ebdb-i18n-countries-pref-scripts nil
  "An alist equivalent to `ebdb-i18n-countries', but in alternate scripts.
Ie, each alist element is a cons of a country name, in a
non-English script, plus the same three-letter symbol as found in
`ebdb-i18n-countries'.  This is meant to allow country names to
be listed in the country's own script, but the name can be given
in any script the user prefers.

Any country name listed here will be offered along with the
English version for completion, and will be preferred over the
English version for display."

  :type 'list
  :group 'ebdb-i18n)

;; defvars come first to pacify compiler.

;; Taken from https://en.wikipedia.org/wiki/ISO_3166-1_alpha-3, on Feb
;; 27, 2016
(defvar ebdb-i18n-countries
  '(
("Afghanistan" . afg)
("Åland Islands" . ala)
("Albania" . alb)
("Algeria" . dza)
("American Samoa" . asm)
("Andorra" . and)
("Angola" . ago)
("Anguilla" . aia)
("Antarctica" . ata)
("Antigua and Barbuda" . atg)
("Argentina" . arg)
("Armenia" . arm)
("Aruba" . abw)
("Australia" . aus)
("Austria" . aut)
("Azerbaijan" . aze)
("Bahamas" . bhs)
("Bahrain" . bhr)
("Bangladesh" . bgd)
("Barbados" . brb)
("Belarus" . blr)
("Belgium" . bel)
("Belize" . blz)
("Benin" . ben)
("Bermuda" . bmu)
("Bhutan" . btn)
("Bolivia" . bol)
("Bonaire" . bes)
("Sint Eustatius" . bes)
("Saba" . bes)
("Bosnia and Herzegovina" . bih)
("Botswana" . bwa)
("Bouvet Island" . bvt)
("Brazil" . bra)
("British Indian Ocean Territory" . iot)
("Brunei Darussalam" . brn)
("Bulgaria" . bgr)
("Burkina Faso" . bfa)
("Burundi" . bdi)
("Cabo Verde" . cpv)
("Cambodia" . khm)
("Cameroon" . cmr)
("Canada" . can)
("Cayman Islands" . cym)
("Central African Republic" . caf)
("Chad" . tcd)
("Chile" . chl)
("China" . chn)
("Christmas Island" . cxr)
("Cocos (Keeling) Islands" . cck)
("Colombia" . col)
("Comoros" . com)
("Congo" . cog)
("Congo" . cod)
("Cook Islands" . cok)
("Costa Rica" . cri)
("Côte d'Ivoire" . civ)
("Croatia" . hrv)
("Cuba" . cub)
("Curaçao" . cuw)
("Cyprus" . cyp)
("Czech Republic" . cze)
("Denmark" . dnk)
("Djibouti" . dji)
("Dominica" . dma)
("Dominican Republic" . dom)
("Ecuador" . ecu)
("Egypt" . egy)
("El Salvador" . slv)
("Emacs" . emc)
("Equatorial Guinea" . gnq)
("Eritrea" . eri)
("Estonia" . est)
("Ethiopia" . eth)
("Falkland Islands" . flk)
("Faroe Islands" . fro)
("Fiji" . fji)
("Finland" . fin)
("France" . fra)
("French Guiana" . guf)
("French Polynesia" . pyf)
("French Southern Territories" . atf)
("Gabon" . gab)
("Gambia" . gmb)
("Georgia" . geo)
("Germany" . deu)
("Ghana" . gha)
("Gibraltar" . gib)
("Greece" . grc)
("Greenland" . grl)
("Grenada" . grd)
("Guadeloupe" . glp)
("Guam" . gum)
("Guatemala" . gtm)
("Guernsey" . ggy)
("Guinea" . gin)
("Guinea-Bissau" . gnb)
("Guyana" . guy)
("Haiti" . hti)
("Heard Island and McDonald Islands" . hmd)
("Holy See" . vat)
("Honduras" . hnd)
("Hong Kong" . hkg)
("Hungary" . hun)
("Iceland" . isl)
("India" . ind)
("Indonesia" . idn)
("Iran" . irn)
("Iraq" . irq)
("Ireland" . irl)
("Isle of Man" . imn)
("Israel" . isr)
("Italy" . ita)
("Jamaica" . jam)
("Japan" . jpn)
("Jersey" . jey)
("Jordan" . jor)
("Kazakhstan" . kaz)
("Kenya" . ken)
("Kiribati" . kir)
("North Korea" . prk)
("South Korea" . kor)
("Kuwait" . kwt)
("Kyrgyzstan" . kgz)
("Laos" . lao)
("Lao People's Democratic Republic" . lao)
("Latvia" . lva)
("Lebanon" . lbn)
("Lesotho" . lso)
("Liberia" . lbr)
("Libya" . lby)
("Liechtenstein" . lie)
("Lithuania" . ltu)
("Luxembourg" . lux)
("Macao" . mac)
("Macedonia" . mkd)
("Madagascar" . mdg)
("Malawi" . mwi)
("Malaysia" . mys)
("Maldives" . mdv)
("Mali" . mli)
("Malta" . mlt)
("Marshall Islands" . mhl)
("Martinique" . mtq)
("Mauritania" . mrt)
("Mauritius" . mus)
("Mayotte" . myt)
("Mexico" . mex)
("Micronesia" . fsm)
("Moldova" . mda)
("Monaco" . mco)
("Mongolia" . mng)
("Montenegro" . mne)
("Montserrat" . msr)
("Morocco" . mar)
("Mozambique" . moz)
("Myanmar" . mmr)
("Namibia" . nam)
("Nauru" . nru)
("Nepal" . npl)
("Netherlands" . nld)
("New Caledonia" . ncl)
("New Zealand" . nzl)
("Nicaragua" . nic)
("Niger" . ner)
("Nigeria" . nga)
("Niue" . niu)
("Norfolk Island" . nfk)
("Northern Mariana Islands" . mnp)
("Norway" . nor)
("Oman" . omn)
("Pakistan" . pak)
("Palau" . plw)
("Palestine" . pse)
("Panama" . pan)
("Papua New Guinea" . png)
("Paraguay" . pry)
("Peru" . per)
("Philippines" . phl)
("Pitcairn" . pcn)
("Poland" . pol)
("Portugal" . prt)
("Puerto Rico" . pri)
("Qatar" . qat)
("Réunion" . reu)
("Romania" . rou)
("Russian Federation" . rus)
("Rwanda" . rwa)
("Saint Barthélemy" . blm)
("Saint Helena, Ascension and Tristan da Cunha" . shn)
("Saint Kitts and Nevis" . kna)
("Saint Lucia" . lca)
("Saint Martin" . maf)
("Saint Pierre and Miquelon" . spm)
("Saint Vincent and the Grenadines" . vct)
("Samoa" . wsm)
("San Marino" . smr)
("Sao Tome and Principe" . stp)
("Saudi Arabia" . sau)
("Senegal" . sen)
("Serbia" . srb)
("Seychelles" . syc)
("Sierra Leone" . sle)
("Singapore" . sgp)
("Sint Maarten" . sxm)
("Slovakia" . svk)
("Slovenia" . svn)
("Solomon Islands" . slb)
("Somalia" . som)
("South Africa" . zaf)
("South Georgia" . sgs)
("South Georgia and the South Sandwich Islands" . sgs)
("South Sudan" . ssd)
("Spain" . esp)
("Sri Lanka" . lka)
("Sudan" . sdn)
("Suriname" . sur)
("Svalbard and Jan Mayen" . sjm)
("Swaziland" . swz)
("Sweden" . swe)
("Switzerland" . che)
("Syrian Arab Republic" . syr)
("Taiwan" . twn)
("Tajikistan" . tjk)
("Tanzania" . tza)
("Thailand" . tha)
("Timor-Leste" . tls)
("Togo" . tgo)
("Tokelau" . tkl)
("Tonga" . ton)
("Trinidad and Tobago" . tto)
("Tunisia" . tun)
("Turkey" . tur)
("Turkmenistan" . tkm)
("Turks and Caicos Islands" . tca)
("Tuvalu" . tuv)
("Uganda" . uga)
("Ukraine" . ukr)
("UAE" . are)
("United Arab Emirates" . are)
("UK" . gbr)
("United Kingdom of Great Britain and Northern Ireland" . gbr)
("USA" . usa)
("United States of America" . usa)
("United States Minor Outlying Islands" . umi)
("Uruguay" . ury)
("Uzbekistan" . uzb)
("Vanuatu" . vut)
("Venezuela" . ven)
("Viet Nam" . vnm)
("Virgin Islands (British)" . vgb)
("Virgin Islands (U.S.)" . vir)
("Wallis and Futuna" . wlf)
("Western Sahara" . esh)
("Yemen" . yem)
("Zambia" . zmb)
("Zimbabwe" . zwe))
  "Mapping between a string label for countries or regions, in
English, and a three-letter symbol identifying the country, as
per ISO 3166-1 alpha 3.")

(defsubst ebdb-i18n-countries ()
  (append ebdb-i18n-countries-pref-scripts
	  ebdb-i18n-countries))

;; Taken from https://en.wikipedia.org/wiki/Telephone_country_codes,
;; on Jul 30, 2016
(defvar ebdb-i18n-phone-codes
  '(
    ;; Need a different way of doing this.
    ;; ("Abkhazia" . ((7 (840 940)) (995 44)))
("Afghanistan" . 93)
("Åland Islands" . (358 18))
("Albania" . 355)
("Algeria" . 213)
("American Samoa" . (1 684))
("Andorra" . 376)
("Angola" . 244)
("Anguilla" . (1 264))
("Antigua and Barbuda" . (1 268))
("Argentina" . 54)
("Armenia" . 374)
("Aruba" . 297)
("Ascension" . 247)
("Australia" . 61)
("Australian External Territories" . 672)
("Austria" . 43)
("Azerbaijan" . 994)
("Bahamas" . (1 242))
("Bahrain" . 973)
("Bangladesh" . 880)
("Barbados" . (1 246))
("Barbuda" . (1 268))
("Belarus" . 375)
("Belgium" . 32)
("Belize" . 501)
("Benin" . 229)
("Bermuda" . (1 441))
("Bhutan" . 975)
("Bolivia" . 591)
("Bonaire" . (599 7))
("Bosnia and Herzegovina" . 387)
("Botswana" . 267)
("Brazil" . 55)
("British Indian Ocean Territory" . 246)
("British Virgin Islands" . (1 284))
("Brunei Darussalam" . 673)
("Bulgaria" . 359)
("Burkina Faso" . 226)
("Burundi" . 257)
("Cambodia" . 855)
("Cameroon" . 237)
("Canada" . 1)
("Cape Verde" . 238)
("Caribbean Netherlands" . (599 (3 4 7)))
("Cayman Islands" . (1 345))
("Central African Republic" . 236)
("Chad" . 235)
("Chatham Island, New Zealand" . 64)
("Chile" . 56)
("China" . 86)
("Christmas Island" . 61)
("Cocos (Keeling) Islands" . 61)
("Colombia" . 57)
("Comoros" . 269)
("Congo" . 242)
("Congo, Democratic Republic of the (Zaire)" . 243)
("Cook Islands" . 682)
("Costa Rica" . 506)
("Ivory Coast" . 225)
("Croatia" . 385)
("Cuba" . 53)
("Guantanamo Bay, Cuba" . (53 99))
("Curaçao" . (599 9))
("Cyprus" . 357)
("Czech Republic" . 420)
("Denmark" . 45)
("Diego Garcia" . 246)
("Djibouti" . 253)
("Dominica" . (1 767))
("Dominican Republic" . (1 (809 829 849)))
("East Timor" . 670)
("Easter Island" . 56)
("Ecuador" . 593)
("Egypt" . 20)
("El Salvador" . 503)
("Ellipso (Mobile Satellite service)" . (881 (2 3)))
("EMSAT (Mobile Satellite service)" . (882 13))
("Equatorial Guinea" . 240)
("Eritrea" . 291)
("Estonia" . 372)
("Ethiopia" . 251)
("Falkland Islands" . 500)
("Faroe Islands" . 298)
("Fiji" . 679)
("Finland" . 358)
("France" . 33)
("French Antilles" . 596)
("French Guiana" . 594)
("French Polynesia" . 689)
("Gabon" . 241)
("Gambia" . 220)
("Georgia" . 995)
("Germany" . 49)
("Ghana" . 233)
("Gibraltar" . 350)
("Global Mobile Satellite System (GMSS)" . 881)
("Globalstar (Mobile Satellite Service)" . (881 (8 9)))
("Greece" . 30)
("Greenland" . 299)
("Grenada" . (1 473))
("Guadeloupe" . 590)
("Guam" . (1 671))
("Guatemala" . 502)
("Guernsey" . 44)
("Guinea" . 224)
("Guinea-Bissau" . 245)
("Guyana" . 592)
("Haiti" . 509)
("Honduras" . 504)
("Hong Kong" . 852)
("Hungary" . 36)
("Iceland" . 354)
("ICO Global (Mobile Satellite Service)" . (881 (0 1)))
("India" . 91)
("Indonesia" . 62)
("Inmarsat SNAC" . 870)
("International Freephone Service" . 800)
("International Shared Cost Service (ISCS)" . 808)
("Iran" . 98)
("Iraq" . 964)
("Ireland" . 353)
("Iridium (Mobile Satellite service)" . (881 (6 7)))
("Isle of Man" . 44)
("Israel" . 972)
("Italy" . 39)
("Jamaica" . (1 876))
("Jan Mayen" . (47 79))
("Japan" . 81)
("Jersey" . 44)
("Jordan" . 962)
("Kazakhstan" . (7 (6 7)))
("Kenya" . 254)
("Kiribati" . 686)
("Korea, North" . 850)
("Korea, South" . 82)
("Kuwait" . 965)
("Kyrgyzstan" . 996)
("Laos" . 856)
("Latvia" . 371)
("Lebanon" . 961)
("Lesotho" . 266)
("Liberia" . 231)
("Libya" . 218)
("Liechtenstein" . 423)
("Lithuania" . 370)
("Luxembourg" . 352)
("Macau" . 853)
("Macedonia" . 389)
("Madagascar" . 261)
("Malawi" . 265)
("Malaysia" . 60)
("Maldives" . 960)
("Mali" . 223)
("Malta" . 356)
("Marshall Islands" . 692)
("Martinique" . 596)
("Mauritania" . 222)
("Mauritius" . 230)
("Mayotte" . 262)
("Mexico" . 52)
("Micronesia, Federated States of" . 691)
("Midway Island, USA" . (1 808))
("Moldova" . 373)
("Monaco" . 377)
("Mongolia" . 976)
("Montenegro" . 382)
("Montserrat" . (1 664))
("Morocco" . 212)
("Mozambique" . 258)
("Myanmar" . 95)
("Namibia" . 264)
("Nauru" . 674)
("Nepal" . 977)
("Netherlands" . 31)
("Nevis" . (1 869))
("New Caledonia" . 687)
("New Zealand" . 64)
("Nicaragua" . 505)
("Niger" . 227)
("Nigeria" . 234)
("Niue" . 683)
("Norfolk Island" . 672)
("Northern Cyprus" . (90 392))
("Northern Mariana Islands" . (1 670))
("Norway" . 47)
("Oman" . 968)
("Pakistan" . 92)
("Palau" . 680)
("Palestine, State of" . 970)
("Panama" . 507)
("Papua New Guinea" . 675)
("Paraguay" . 595)
("Peru" . 51)
("Philippines" . 63)
("Pitcairn Islands" . 64)
("Poland" . 48)
("Portugal" . 351)
("Puerto Rico" . (1 (787 939)))
("Qatar" . 974)
("Réunion" . 262)
("Romania" . 40)
("Russia" . 7)
("Rwanda" . 250)
("Saba" . (599 4))
("Saint Barthélemy" . 590)
("Saint Helena" . 290)
("Saint Kitts and Nevis" . (1 869))
("Saint Lucia" . (1 758))
("Saint Martin (France)" . 590)
("Saint Pierre and Miquelon" . 508)
("Saint Vincent and the Grenadines" . (1 784))
("Samoa" . 685)
("San Marino" . 378)
("São Tomé and Príncipe" . 239)
("Saudi Arabia" . 966)
("Senegal" . 221)
("Serbia" . 381)
("Seychelles" . 248)
("Sierra Leone" . 232)
("Singapore" . 65)
("Sint Eustatius" . (599 3))
("Sint Maarten (Netherlands)" . (1 721))
("Slovakia" . 421)
("Slovenia" . 386)
("Solomon Islands" . 677)
("Somalia" . 252)
("South Africa" . 27)
("South Georgia and the South Sandwich Islands" . 500)
("South Ossetia" . (995 34))
("South Sudan" . 211)
("Spain" . 34)
("Sri Lanka" . 94)
("Sudan" . 249)
("Suriname" . 597)
("Svalbard" . (47 79))
("Swaziland" . 268)
("Sweden" . 46)
("Switzerland" . 41)
("Syria" . 963)
("Taiwan" . 886)
("Tajikistan" . 992)
("Tanzania" . 255)
("Thailand" . 66)
("Thuraya (Mobile Satellite service)" . (882 16))
("Togo" . 228)
("Tokelau" . 690)
("Tonga" . 676)
("Trinidad and Tobago" . (1 868))
("Tristan da Cunha" . (290 8))
("Tunisia" . 216)
("Turkey" . 90)
("Turkmenistan" . 993)
("Turks and Caicos Islands" . (1 649))
("Tuvalu" . 688)
("Uganda" . 256)
("Ukraine" . 380)
("United Arab Emirates" . 971)
("UK" . 44)
("United Kingdom" . 44)
("USA" . 1)
("United States" . 1)
("Universal Personal Telecommunications (UPT)" . 878)
("Uruguay" . 598)
("US Virgin Islands" . (1 340))
("Uzbekistan" . 998)
("Vanuatu" . 678)
("Venezuela" . 58)
;; What does this three-part number even mean?
;; ("Vatican City State (Holy See)" . (39 06 698))
("Vietnam" . 84)
("Wake Island, USA" . (1 808))
("Wallis and Futuna" . 681)
("Yemen" . 967)
("Zambia" . 260)
("Zanzibar" . 255)
("Zimbabwe" .  263))
  "Mapping of country names to country-code numbers.")

(cl-defgeneric ebdb-read-i18n (class slots obj spec)
  "An internationalized version of `ebdb-read'.

This works the same as `ebdb-read', plus an additional argument
SPEC.  What SPEC is depends on CLASS, but might be a phone
country code, or a country symbol, or a script symbol.

This method should return a plist of slots for object creation.")

(cl-defgeneric ebdb-parse-i18n (class string spec &optional slots)
  "An internationalized version of `ebdb-parse'.

This works the same as `ebdb-read', plus an additional argument
SPEC.  What SPEC is depends on CLASS, but might be a phone
country code, or a country symbol, or a script symbol.  SLOTS is
a plist of existing slot values.

This method should return a new instance of CLASS.")

(cl-defgeneric ebdb-string-i18n (field spec)
  "An internationalized version of `ebdb-string'.")

(cl-defgeneric ebdb-init-field-i18n (field record spec)
  "An internationalized version of `ebdb-init-field'.")

(cl-defgeneric ebdb-delete-field-i18n (field record spec unload)
  "An internationalized version of `ebdb-delete-field'.")

(cl-defmethod ebdb-parse-i18n :around (_class _string _spec &optional _slots)
  "Don't clobber match data when testing names."
  (save-match-data
    (cl-call-next-method)))

;;;###autoload
(defun ebdb-internationalize-addresses ()
  "Go through all the EBDB contacts and \"internationalize\"
  address fields.

Essentially this just means swapping out the string country names
for their symbol representations."
  (let ((count 0))
    (dolist (rec (ebdb-records))
      (dolist (adr (ebdb-record-address rec))
	(when (stringp (slot-value adr 'country))
	  (ignore-errors
	   (ebdb-record-change-field
	    rec adr
	    (clone adr :country
		   (cdr (assoc-string (slot-value adr 'country)
				      (ebdb-i18n-countries)))))
	   (cl-incf count)))))
    (message "Internationalized %d addresses" count)))

(cl-defmethod ebdb-read :extra "i18n" ((class (subclass ebdb-field-address))
				       &optional slots obj)
  (let ((country
	  (cdr (assoc (completing-read
		       "Country: "
		       (ebdb-i18n-countries)
		       nil nil
		       (when obj (car (rassoc (ebdb-address-country obj)
					      (ebdb-i18n-countries)))))
		      (ebdb-i18n-countries)))))
    (setq slots
	  (condition-case nil
	      (ebdb-read-i18n class country
			      (plist-put slots :country country) obj)
	    (cl-no-method
	     (plist-put slots :country country))))
    (cl-call-next-method class slots obj)))

(cl-defmethod ebdb-string :extra "i18n" ((adr ebdb-field-address))
  "Internationally-aware version of `ebdb-string' for addresses."
  (let ((cc (slot-value adr 'country)))
    (or (and cc
	     (symbolp cc)
	     (condition-case nil
		 (ebdb-string-i18n adr cc)
	       (cl-no-method nil)))
	(cl-call-next-method))))

;; This is not an :extra method, because there will never be a
;; non-i18n `ebdb-parse' method for addresses.  It's just too hard to
;; guess if you don't know the country.  This is only used in
;; snarfing.

(cl-defmethod ebdb-parse ((class (subclass ebdb-field-address))
			  (str string)
			  &optional slots)
  "Internationally-aware version of `ebdb-parse' for addresses."
  (let ((cc (or (plist-get slots :country)
		(when (string-match (regexp-opt
				     (mapcar
				      (lambda (elt) (car elt))
				      (ebdb-i18n-countries)))
				    str)
		  (cdr-safe (assoc-string
			     (match-string 0 str)
			     (ebdb-i18n-countries)))))))
    (or (and cc
	     (symbolp cc)
	     (condition-case nil
		 (ebdb-parse-i18n class str cc slots)
	       (cl-no-method nil)))
	(signal 'ebdb-unparseable (list str)))))

(cl-defmethod ebdb-read :extra "i18n" ((class (subclass ebdb-field-phone))
				       &optional slots obj)
  (let ((country
	 (if obj
	     (slot-value obj 'country-code)
	   (cdr (assoc (completing-read
			"Country/Region: "
			ebdb-i18n-phone-codes nil nil)
		       ebdb-i18n-phone-codes))))
	(area-code (when obj (slot-value obj 'area-code))))
    ;; Obviously this whole structure thing is just poorly
    ;; thought-out.
    (when (consp country)
      (cond ((numberp (car country))
	     (setq area-code (cl-second country)
		   country (car country)))
	    ((consp (car country))
	     (setq country (assoc
			    (string-to-number
			     (completing-read
			      "Choose: "
			      (mapcar (lambda (x)
					(number-to-string (car x)))
				      country)))
			    country)
		   area-code (cl-second country))))
      (when (consp area-code)
	(setq area-code (string-to-number
			 (completing-read
			  "Area code: "
			  (mapcar #'number-to-string area-code))))))
    (when area-code
      (setq slots (plist-put slots :area-code area-code)))
    (setq slots (plist-put slots :country-code country))
    (setq slots
	  (condition-case nil
	      (ebdb-read-i18n class slots obj country)
	    (cl-no-method
	     slots)))
    (cl-call-next-method class slots obj)))

(cl-defmethod ebdb-string :extra "i18n" ((phone ebdb-field-phone))
  "Internationally-aware version of `ebdb-string' for phones."
  (let ((cc (slot-value phone 'country-code)))
    (or (and cc
	     (condition-case nil
		 (ebdb-string-i18n phone cc)
	       (cl-no-method nil)))
	(cl-call-next-method))))

(cl-defmethod ebdb-parse :extra "i18n" ((class (subclass ebdb-field-phone))
					(str string)
					&optional slots)
  (let ((cc (or (plist-get slots :country-code)
		(and (string-match "\\`(?\\+(?\\([0-9]\\{1,3\\}\\))?[ \t]+" str)
		     (string-to-number (match-string 1 str))))))
    (or (and cc
	     (condition-case nil
		 (ebdb-parse-i18n
		  class
		  (replace-match "" nil nil str 0)
		  cc (plist-put slots :country-code cc))
	       (cl-no-method nil)))
	(cl-call-next-method))))

;; We don't need to override the `ebdb-read' method for names.  It
;; only matters what script the name is in if the user has set
;; `ebdb-read-name-articulate' to nil, in which case the name is
;; passed to this `ebdb-parse' method.
(cl-defmethod ebdb-parse :extra "i18n" ((class (subclass ebdb-field-name-complex))
					(string string)
					&optional slots)
  ;; For now, only test the first character of whatever string the
  ;; user has entered.
  (let ((script (unless (string-empty-p string)
		  (aref char-script-table (aref string 0)))))
    (or (and script
	     (null (memq script ebdb-i18n-ignorable-scripts))
	     (condition-case nil
		 (ebdb-parse-i18n class string script slots)
	       (cl-no-method
		nil)))
	(cl-call-next-method))))

(cl-defmethod ebdb-string :extra "i18n" ((name ebdb-field-name-complex))
  (let* ((str (cl-call-next-method name))
	 (script (aref char-script-table (aref str 0))))
    (unless (memq script ebdb-i18n-ignorable-scripts)
      (condition-case nil
	  (setq str (ebdb-string-i18n name script))
	(cl-no-method nil)))
    str))

(cl-defmethod ebdb-init-field :extra "i18n" ((name ebdb-field-name) &optional record)
  "Do additional initialization work for international names."
  (let* ((res (cl-call-next-method name record))
	 (str (ebdb-string name))
	 (script (aref char-script-table (aref str 0))))
    (unless (memq script ebdb-i18n-ignorable-scripts)
      (condition-case nil
	  (ebdb-init-field-i18n name record script)
	(cl-no-method nil)))
    res))

(cl-defmethod ebdb-delete-field :extra "i18n" ((name ebdb-field-name) &optional record unload)
  "Do additional deletion work for international names."
  (let* ((str (ebdb-string name))
	 (script (aref char-script-table (aref str 0))))
    (unless (memq script ebdb-i18n-ignorable-scripts)
      (condition-case nil
	  (ebdb-delete-field-i18n name record script unload)
	(cl-no-method nil))))
  (cl-call-next-method))

(provide 'ebdb-i18n)
;;; ebdb-i18n.el ends here

;;; Tests for bbdb-vcard.el
;;
;; Before proceeding, you should probably save your production bbdb file.
;;
;; To run the tests, eval this file.
;; In case of failure, find test results in buffer `bbdb-vcard-test-result'.
;;
;; For the sake of minimality, not all test cases are rfc compliant.


(require 'bbdb-vcard)

(defun bbdb-vcard-import-test
  (vcard bbdb-entry search-name
         &optional search-company search-net check-creation-date-p)
  "Import VCARD and search for it in bbdb by SEARCH-NAME,
SEARCH-COMPANY, (perhaps later) SEARCH-NET.  If search result
disagrees with BBDB-ENTRY, talk about it in buffer
bbdb-vcard-test-result. timestamp and, if CHECK-CREATION-DATE-P is
nil, creation-date are not taken into account."
  (bbdb-vcard-iterate-vcards 'bbdb-vcard-import-vcard vcard)
  (let* ((search-company (or search-company ""))
         (bbdb-search-result
          (car (bbdb-search (bbdb-search (bbdb-records) search-name)
                            nil search-company))))
    (setf (cdr (assoc 'timestamp (elt bbdb-search-result 7))) "2010-03-04"
          (cdr (assoc 'timestamp (elt bbdb-entry 7))) "2010-03-04")
    (unless check-creation-date-p
      (setf (cdr (assoc 'creation-date (elt bbdb-search-result 7))) "2010-03-04"
            (cdr (assoc 'creation-date (elt bbdb-entry 7))) "2010-03-04"))
    (unless (equal (subseq bbdb-search-result 0 8)
                   (subseq bbdb-entry 0 8))
      (princ "\nTest failed:\n" (get-buffer-create "bbdb-vcard-test-result"))
      (prin1 vcard (get-buffer-create "bbdb-vcard-test-result"))
      (princ "\nwas stored as\n" (get-buffer-create "bbdb-vcard-test-result"))
      (prin1 (subseq bbdb-search-result 0 8)
             (get-buffer-create "bbdb-vcard-test-result"))
      (princ "\nbut was expected as\n" (get-buffer-create "bbdb-vcard-test-result"))
      (prin1 bbdb-entry (get-buffer-create "bbdb-vcard-test-result")))))

(defun bbdb-vcard-normalize-notes (notes)
  "Sort a BBDB NOTES field and delete the timestamps in order to make them
comparable after re-import."
  (let ((notes (remove-alist 'notes 'timestamp)))
    (setq notes (remove-alist 'notes 'creation-date))
    (sort
     notes
     '(lambda (x y) (if (string= (symbol-name (car x)) (symbol-name (car y)))
                        (string< (cdr x) (cdr y))
                      (string< (symbol-name (car x)) (symbol-name (car y))))))))

(defun bbdb-vcard-normalize-record (record)
  "Make BBDB RECORD comparable by deleting certain things and sorting others."
  (setf (elt record 6) (bbdb-vcard-normalize-notes (elt record 7)))
  (subseq record 0 7))

(defun bbdb-vcard-compare-bbdbs (first-bbdb second-bbdb)
  "Compare two BBDB record lists. Tell about mismatches in buffer
`bbdb-vcard-test-result'."
  (let ((i 0)
        first-record second-record)
    (while (or (nth i first-bbdb) (nth i second-bbdb))
      (unless (equal (bbdb-vcard-normalize-record (nth i first-bbdb))
                     (bbdb-vcard-normalize-record (nth i second-bbdb)))
        (princ "\nRe-import: comparison of these records failed:"
               (get-buffer-create "bbdb-vcard-test-result"))
        (print (bbdb-vcard-normalize-record (nth i first-bbdb))
               (get-buffer-create "bbdb-vcard-test-result"))
        (prin1 (bbdb-vcard-normalize-record (nth i second-bbdb))
               (get-buffer-create "bbdb-vcard-test-result")))
      (incf i))))


;;; Try not to mess up our real BBDB:
(when bbdb-buffer
  (save-buffer bbdb-buffer)
  (kill-buffer bbdb-buffer))
(when (get-buffer "test-bbdb") (kill-buffer "test-bbdb"))
(setq bbdb-file "/tmp/test-bbdb")
(when (file-exists-p bbdb-file) (delete-file bbdb-file))
(when (get-buffer "bbdb-vcard-test-result") (kill-buffer "bbdb-vcard-test-result"))


;;;; The Import Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(bbdb-vcard-import-test
 "
** A vcard without any type parameters.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:First1 Last1
N:Last1;First1
NICKNAME:Firsty1
PHOTO:The Alphabet:
 abcdefghijklmnop
 qrstuvwsyz
BDAY:1999-12-05
ADR:Box111;Room 111;First Street,First Corner;Cityone;First State;11111;Country
LABEL:Label 1
TEL:+11111111
EMAIL:first1@provider1
MAILER:Wanderlust1
TZ:+01:00
GEO:37.386013;-122.082932
TITLE:Director\\, Research and Development
ROLE:Programmer
LOGO:encoded logo #1
AGENT:CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com
ORG:Company1;Unit1;Subunit1
CATEGORIES:category1
NOTE:This vcard uses every type defined in rfc2426.
PRODID:-//ONLINE DIRECTORY//NONSGML Version 1//EN
REV:1995-10-31T22:27:10Z
SORT-STRING:aaa000
SOUND:Audible1
UID:111-111-111-111
URL:http://first1.host1.org
CLASS:CONFIDENTIAL
KEY:The Key No 1
X-foo:extended type 1
END:VCARD
"
 ["First1" "Last1"
  ("Firsty1")
  "Company1
Unit1
Subunit1"
  (["Office" "+11111111"])
  (["Office"
    ("Box111" "Room 111" "First Street" "First Corner")
    "Cityone"
    "First State"
    "11111"
    "Country"])
  ("first1@provider1")
  ((x-foo . "extended type 1")
   (key . "The Key No 1")
   (class . "CONFIDENTIAL")
   (uid . "111-111-111-111")
   (sound . "Audible1")
   (sort-string . "aaa000")
   (prodid . "-//ONLINE DIRECTORY//NONSGML Version 1//EN")
   (agent . "CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com")
   (logo . "encoded logo #1")
   (role . "Programmer")
   (title . "Director, Research and Development")
   (geo . "37.386013;-122.082932")
   (tz . "+01:00")
   (mailer . "Wanderlust1")
   (label . "Label 1")
   (photo . "The Alphabet:abcdefghijklmnopqrstuvwsyz")
   (mail-alias . "category1")
   (anniversary . "1999-12-05 birthday")
   (notes . "This vcard uses every type defined in rfc2426.")
   (www . "http://first1.host1.org")
   (creation-date . "1995-10-31T22:27:10Z") (timestamp . "2010-03-04"))]
 "First1 Last1"
 nil nil t)


(bbdb-vcard-import-test
 "
** Bad vCard: semi-colons where they don't belong
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:First2; Last2
N:Last2;First2
NICKNAME:Firsty2,or; something
PHOTO:The Alphabet:
 abcdefghij;klmnop
 qrstuvwsyz
BDAY:1999-12-05
ADR:Box111;Room 111;First Street,First Corner;Cityone;First State;11111;Country
LABEL:Label 1;Label 2
TEL:+11111111;+222222
EMAIL:first1@provider1
MAILER:Wanderlust1;Wanderlust2
TZ:+01:00;Here
GEO:37.386013;-122.082932
TITLE:Director\\, Research; and Development
ROLE:Programmer
LOGO:encoded logo #1
AGENT:CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com
ORG:Company1;Unit1;Subunit1
CATEGORIES:category1
NOTE:This isn't a decent vCard. It shouldn't render our bbdb unusable. We don't expect it to re-import unchanged, though.
REV:1995-10-31T22:27:10Z
SORT-STRING:aaa000
SOUND:Audible1
UID:111-111-111-111
URL:http://first1.host1.org; My home
CLASS:CONFIDENTIAL
KEY:The Key No 1
X-foo:extended type 1
END:VCARD
"
 ["First2" "Last2"
  ("First2; Last2" "Firsty2" "or; something")
  "Company1
Unit1
Subunit1"
  (["Office" "+11111111;+222222"])
  (["Office" ("Box111" "Room 111" "First Street" "First Corner") "Cityone" "First State" "11111" "Country"])
  ("first1@provider1")
  ((x-foo . "extended type 1")
   (key . "The Key No 1")
   (class . "CONFIDENTIAL")
   (uid . "111-111-111-111")
   (sound . "Audible1")
   (sort-string . "aaa000")
   (agent . "CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com")
   (logo . "encoded logo #1")
   (role . "Programmer")
   (title . "Director, Research; and Development")
   (geo . "37.386013;-122.082932")
   (tz . "+01:00;Here")
   (mailer . "Wanderlust1;Wanderlust2")
   (label . "Label 1;Label 2")
   (photo . "The Alphabet:abcdefghij;klmnopqrstuvwsyz")
   (mail-alias . "category1")
   (anniversary . "1999-12-05 birthday")
   (notes . "This isn't a decent vCard. It shouldn't render our bbdb unusable. We don't expect it to re-import unchanged, though.")
   (www . "http://first1.host1.org; My home")
   (creation-date . "1995-10-31T22:27:10Z") (timestamp . "2010-03-04"))]
  "First2 Last2"
 nil nil t)


(bbdb-vcard-import-test
 "
** The following is made of examples from rfc2426.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:Mr. John Q. Public\\, Esq.
N:Stevenson;John;Philip,Paul;Dr.;Jr.,M.D.,A.C.P.
NICKNAME:Robbie
PHOTO;VALUE=uri:http://www.abc.com/pub/photos
 /jqpublic.gif
BDAY:1996-04-15
ADR;TYPE=dom,home,postal,parcel:;;123 Main
  Street;Any Town;CA;91921-1234
LABEL;TYPE=dom,home,postal,parcel:Mr.John Q. Public\\, Esq.\\n
 Mail Drop: TNE QB\\n123 Main Street\\nAny Town\\, CA  91921-1234
 \\nU.S.A.
TEL;TYPE=work,voice,pref,msg:+1-213-555-1234
EMAIL;TYPE=internet:jqpublic@xyz.dom1.com
EMAIL;TYPE=internet:jdoe@isp.net
MAILER:PigeonMail 2.1
TZ:-05:00
GEO:37.386013;-122.082932
TITLE:Director\\, Research and Development
ROLE:Programmer
LOGO;ENCODING=b;TYPE=JPEG:MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcN
 AQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bm
 ljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0
AGENT;VALUE=uri:
 CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com
ORG:ABC\\, Inc.;North American Division;Marketing
CATEGORIES:TRAVEL AGENT
NOTE:This fax number is operational 0800 to 1715
  EST\\, Mon-Fri.
PRODID:-//ONLINE DIRECTORY//NONSGML Version 1//EN
REV:1995-10-31T22:27:10Z
SOUND;TYPE=BASIC;ENCODING=b:MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcN
 AQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bm
 ljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0
UID:19950401-080045-40000F192713-0052
URL:http://www.swbyps.restaurant.french/~chezchic.html
CLASS:PUBLIC
KEY;ENCODING=b:MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQA
 wdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENbW11bmljYX
 Rpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0
 ZW1zMRwwGgYDVQQDExNyb290Y2EubmV0c2NhcGUuY29tMB4XDTk3MDYwNj
 E5NDc1OVoXDTk3MTIwMzE5NDc1OVowgYkxCzAJBgNVBAYTAlVTMSYwJAYD
 VQQKEx1OZXRzY2FwZSBDb21tdW5pY2F0aW9ucyBDb3JwLjEYMBYGA1UEAx
 MPVGltb3RoeSBBIEhvd2VzMSEwHwYJKoZIhvcNAQkBFhJob3dlc0BuZXRz
 Y2FwZS5jb20xFTATBgoJkiaJk/IsZAEBEwVob3dlczBcMA0GCSqGSIb3DQ
 EBAQUAA0sAMEgCQQC0JZf6wkg8pLMXHHCUvMfL5H6zjSk4vTTXZpYyrdN2
 dXcoX49LKiOmgeJSzoiFKHtLOIboyludF90CgqcxtwKnAgMBAAGjNjA0MB
 EGCWCGSAGG+EIBAQQEAwIAoDAfBgNVHSMEGDAWgBT84FToB/GV3jr3mcau
 +hUMbsQukjANBgkqhkiG9w0BAQQFAAOBgQBexv7o7mi3PLXadkmNP9LcIP
 mx93HGp0Kgyx1jIVMyNgsemeAwBM+MSlhMfcpbTrONwNjZYW8vJDSoi//y
 rZlVt9bJbs7MNYZVsyF1unsqaln4/vy6Uawfg8VUMk1U7jt8LYpo4YULU7
 UZHPYVUaSgVttImOHZIKi4hlPXBOhcUQ==
END:VCARD
"
 ["Dr. John Philip Paul" "Stevenson Jr. M.D. A.C.P."
  ("Mr. John Q. Public, Esq." "Robbie")
  "ABC, Inc.
North American Division
Marketing"
  (["Office" "+1-213-555-1234"])
  (["Home"
    ("123 Main Street")
    "Any Town"
    "CA"
    "91921-1234"
    ""])
  ("jqpublic@xyz.dom1.com" "jdoe@isp.net")
  ((key\;encoding=b . "MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENbW11bmljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0ZW1zMRwwGgYDVQQDExNyb290Y2EubmV0c2NhcGUuY29tMB4XDTk3MDYwNjE5NDc1OVoXDTk3MTIwMzE5NDc1OVowgYkxCzAJBgNVBAYTAlVTMSYwJAYDVQQKEx1OZXRzY2FwZSBDb21tdW5pY2F0aW9ucyBDb3JwLjEYMBYGA1UEAxMPVGltb3RoeSBBIEhvd2VzMSEwHwYJKoZIhvcNAQkBFhJob3dlc0BuZXRzY2FwZS5jb20xFTATBgoJkiaJk/IsZAEBEwVob3dlczBcMA0GCSqGSIb3DQEBAQUAA0sAMEgCQQC0JZf6wkg8pLMXHHCUvMfL5H6zjSk4vTTXZpYyrdN2dXcoX49LKiOmgeJSzoiFKHtLOIboyludF90CgqcxtwKnAgMBAAGjNjA0MBEGCWCGSAGG+EIBAQQEAwIAoDAfBgNVHSMEGDAWgBT84FToB/GV3jr3mcau+hUMbsQukjANBgkqhkiG9w0BAQQFAAOBgQBexv7o7mi3PLXadkmNP9LcIPmx93HGp0Kgyx1jIVMyNgsemeAwBM+MSlhMfcpbTrONwNjZYW8vJDSoi//yrZlVt9bJbs7MNYZVsyF1unsqaln4/vy6Uawfg8VUMk1U7jt8LYpo4YULU7UZHPYVUaSgVttImOHZIKi4hlPXBOhcUQ==")
   (class . "PUBLIC")
   (uid . "19950401-080045-40000F192713-0052")
   (sound\;type=basic\;encoding=b . "MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bmljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0")
   (prodid . "-//ONLINE DIRECTORY//NONSGML Version 1//EN")
   (agent\;value=uri . "CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com")
   (logo\;encoding=b\;type=jpeg . "MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bmljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0")
   (role . "Programmer")
   (title . "Director, Research and Development")
   (geo . "37.386013;-122.082932")
   (tz . "-05:00")
   (mailer . "PigeonMail 2.1")
   (label\;type=dom\,home\,postal\,parcel . "Mr.John Q. Public, Esq.
Mail Drop: TNE QB
123 Main Street
Any Town, CA  91921-1234
U.S.A.")
   (photo\;value=uri . "http://www.abc.com/pub/photos/jqpublic.gif")
   (mail-alias . "TRAVEL AGENT")
   (anniversary . "1996-04-15 birthday")
   (notes . "This fax number is operational 0800 to 1715 EST, Mon-Fri.")
   (www . "http://www.swbyps.restaurant.french/~chezchic.html")
   (creation-date . "1995-10-31T22:27:10Z") (timestamp . "2010-03-04"))]
 "John"
 nil nil t)


(bbdb-vcard-import-test
 "
** Exactly the same as before.
   Re-reading it shouldn't duplicate anything.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:Mr. John Q. Public\\, Esq.
N:Stevenson;John;Philip,Paul;Dr.;Jr.,M.D.,A.C.P.
NICKNAME:Robbie
PHOTO;VALUE=uri:http://www.abc.com/pub/photos
 /jqpublic.gif
BDAY:1996-04-15
ADR;TYPE=dom,home,postal,parcel:;;123 Main
  Street;Any Town;CA;91921-1234
LABEL;TYPE=dom,home,postal,parcel:Mr.John Q. Public\\, Esq.\\n
 Mail Drop: TNE QB\\n123 Main Street\\nAny Town\\, CA  91921-1234
 \\nU.S.A.
TEL;TYPE=work,voice,pref,msg:+1-213-555-1234
EMAIL;TYPE=internet:jqpublic@xyz.dom1.com
EMAIL;TYPE=internet:jdoe@isp.net
MAILER:PigeonMail 2.1
TZ:-05:00
GEO:37.386013;-122.082932
TITLE:Director\\, Research and Development
ROLE:Programmer
LOGO;ENCODING=b;TYPE=JPEG:MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcN
 AQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bm
 ljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0
AGENT;VALUE=uri:
 CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com
ORG:ABC\\, Inc.;North American Division;Marketing
CATEGORIES:TRAVEL AGENT
NOTE:This fax number is operational 0800 to 1715
  EST\\, Mon-Fri.
PRODID:-//ONLINE DIRECTORY//NONSGML Version 1//EN
REV:1995-10-31T22:27:10Z
SOUND;TYPE=BASIC;ENCODING=b:MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcN
 AQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bm
 ljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0
UID:19950401-080045-40000F192713-0052
URL:http://www.swbyps.restaurant.french/~chezchic.html
CLASS:PUBLIC
KEY;ENCODING=b:MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQA
 wdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENbW11bmljYX
 Rpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0
 ZW1zMRwwGgYDVQQDExNyb290Y2EubmV0c2NhcGUuY29tMB4XDTk3MDYwNj
 E5NDc1OVoXDTk3MTIwMzE5NDc1OVowgYkxCzAJBgNVBAYTAlVTMSYwJAYD
 VQQKEx1OZXRzY2FwZSBDb21tdW5pY2F0aW9ucyBDb3JwLjEYMBYGA1UEAx
 MPVGltb3RoeSBBIEhvd2VzMSEwHwYJKoZIhvcNAQkBFhJob3dlc0BuZXRz
 Y2FwZS5jb20xFTATBgoJkiaJk/IsZAEBEwVob3dlczBcMA0GCSqGSIb3DQ
 EBAQUAA0sAMEgCQQC0JZf6wkg8pLMXHHCUvMfL5H6zjSk4vTTXZpYyrdN2
 dXcoX49LKiOmgeJSzoiFKHtLOIboyludF90CgqcxtwKnAgMBAAGjNjA0MB
 EGCWCGSAGG+EIBAQQEAwIAoDAfBgNVHSMEGDAWgBT84FToB/GV3jr3mcau
 +hUMbsQukjANBgkqhkiG9w0BAQQFAAOBgQBexv7o7mi3PLXadkmNP9LcIP
 mx93HGp0Kgyx1jIVMyNgsemeAwBM+MSlhMfcpbTrONwNjZYW8vJDSoi//y
 rZlVt9bJbs7MNYZVsyF1unsqaln4/vy6Uawfg8VUMk1U7jt8LYpo4YULU7
 UZHPYVUaSgVttImOHZIKi4hlPXBOhcUQ==
END:VCARD
"
["Dr. John Philip Paul" "Stevenson Jr. M.D. A.C.P."
 ("Mr. John Q. Public, Esq." "Robbie")
 "ABC, Inc.
North American Division
Marketing"
 (["Office" "+1-213-555-1234"])
 (["Home"
   ("123 Main Street")
   "Any Town"
   "CA"
   "91921-1234"
   ""])
 ("jqpublic@xyz.dom1.com" "jdoe@isp.net")
 ((key\;encoding=b . "MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENbW11bmljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0ZW1zMRwwGgYDVQQDExNyb290Y2EubmV0c2NhcGUuY29tMB4XDTk3MDYwNjE5NDc1OVoXDTk3MTIwMzE5NDc1OVowgYkxCzAJBgNVBAYTAlVTMSYwJAYDVQQKEx1OZXRzY2FwZSBDb21tdW5pY2F0aW9ucyBDb3JwLjEYMBYGA1UEAxMPVGltb3RoeSBBIEhvd2VzMSEwHwYJKoZIhvcNAQkBFhJob3dlc0BuZXRzY2FwZS5jb20xFTATBgoJkiaJk/IsZAEBEwVob3dlczBcMA0GCSqGSIb3DQEBAQUAA0sAMEgCQQC0JZf6wkg8pLMXHHCUvMfL5H6zjSk4vTTXZpYyrdN2dXcoX49LKiOmgeJSzoiFKHtLOIboyludF90CgqcxtwKnAgMBAAGjNjA0MBEGCWCGSAGG+EIBAQQEAwIAoDAfBgNVHSMEGDAWgBT84FToB/GV3jr3mcau+hUMbsQukjANBgkqhkiG9w0BAQQFAAOBgQBexv7o7mi3PLXadkmNP9LcIPmx93HGp0Kgyx1jIVMyNgsemeAwBM+MSlhMfcpbTrONwNjZYW8vJDSoi//yrZlVt9bJbs7MNYZVsyF1unsqaln4/vy6Uawfg8VUMk1U7jt8LYpo4YULU7UZHPYVUaSgVttImOHZIKi4hlPXBOhcUQ==")
  (class . "PUBLIC")
  (uid . "19950401-080045-40000F192713-0052")
  (sound\;type=basic\;encoding=b . "MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bmljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0")
  (prodid . "-//ONLINE DIRECTORY//NONSGML Version 1//EN")
  (agent\;value=uri . "CID:JQPUBLIC.part3.960129T083020.xyzMail@host3.com")
  (logo\;encoding=b\;type=jpeg . "MIICajCCAdOgAwIBAgICBEUwDQYJKoZIhvcNAQEEBQAwdzELMAkGA1UEBhMCVVMxLDAqBgNVBAoTI05ldHNjYXBlIENvbW11bmljYXRpb25zIENvcnBvcmF0aW9uMRwwGgYDVQQLExNJbmZvcm1hdGlvbiBTeXN0")
  (role . "Programmer")
  (title . "Director, Research and Development")
  (geo . "37.386013;-122.082932")
  (tz . "-05:00")
  (mailer . "PigeonMail 2.1")
  (label\;type=dom\,home\,postal\,parcel . "Mr.John Q. Public, Esq.
Mail Drop: TNE QB
123 Main Street
Any Town, CA  91921-1234
U.S.A.")
  (photo\;value=uri . "http://www.abc.com/pub/photos/jqpublic.gif")
  (www . "http://www.swbyps.restaurant.french/~chezchic.html")
  (mail-alias . "TRAVEL AGENT")
  (anniversary . "1996-04-15 birthday")
  (notes . "This fax number is operational 0800 to 1715 EST, Mon-Fri.")
  (creation-date . "1995-10-31T22:27:10Z") (timestamp . "2010-03-04"))]
 "John"
 nil nil t)


(bbdb-vcard-import-test 
 "
** Re-use of existing BBDB entries. 
*** N, ORG, EMAIL
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA;FirstA
ORG:OrgA;UnitA
EMAIL:userA@hostA.example.com
END:vcard
"
 ["FirstA" "FamilyA"
  nil
  "OrgA
UnitA"
  nil
  nil
  ("userA@hostA.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA FamilyA")


(bbdb-vcard-import-test
 "
*** The same again; shouldn't change the previous one.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA;FirstA
ORG:OrgA;UnitA
EMAIL:userA@hostA.example.com
END:VCARD
"
 ["FirstA" "FamilyA"
  nil
  "OrgA
UnitA"
  nil
  nil
  ("userA@hostA.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA FamilyA")


(bbdb-vcard-import-test
 "
*** Same N, same ORG, different EMAIL, which should be added to the previous
    one.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA;FirstA
ORG:OrgA;UnitA
EMAIL:personA@example.com
END:VCARD
"
 ["FirstA" "FamilyA"
  nil
  "OrgA
UnitA"
  nil
  nil
  ("userA@hostA.example.com" "personA@example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA FamilyA")


(bbdb-vcard-import-test
 "
*** Same N, same ORG, no EMAIL; shouldn't change anything.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA;FirstA
ORG:OrgA;UnitA
END:VCARD
"
 ["FirstA" "FamilyA"
  nil
  "OrgA
UnitA"
  nil
  nil
  ("userA@hostA.example.com" "personA@example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA FamilyA")


(bbdb-vcard-import-test
 "
*** Same N, same EMAIL, no ORG; shouldn't change anything.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA;FirstA
EMAIL:userA@hostA.example.com
END:VCARD
"
 ["FirstA" "FamilyA"
  nil
  "OrgA
UnitA"
  nil
  nil
  ("userA@hostA.example.com" "personA@example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA FamilyA")


(bbdb-vcard-import-test
 "
*** Same N, same EMAIL, different ORG by which Company of the previous one
    should be replaced.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA;FirstA
ORG:OrgA;UnitB
EMAIL:userA@hostA.example.com
END:VCARD
"
 ["FirstA" "FamilyA"
  nil
  "OrgA
UnitB"
  nil
  nil
  ("userA@hostA.example.com" "personA@example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA FamilyA")


(bbdb-vcard-import-test
 "
*** Different N, same EMAIL, same ORG; should go into a fresh entry.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyA1;FirstA1
ORG:OrgA;UnitB
EMAIL:userA@hostA.example.com
END:VCARD
"
 ["FirstA1" "FamilyA1"
  nil
  "OrgA
UnitB"
  nil
  nil
  ("userA@hostA.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstA1 FamilyA1")



(bbdb-vcard-import-test
 "
** AKA has various sources; duplicates are being discarded.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyB;FirstB
A.N:PseudonymB;FirstB
FN:The FirstB of FamilyB
A.FN:FirstB1 FamilyB1
B.FN:FirstB2 FamilyB2
C.FN:FirstB FamilyB
NICKNAME:Bee,Effy Bee,FirstB FamilyB
END:VCARD
"
 ["FirstB" "FamilyB"
  ("FirstB2 FamilyB2"
   "FirstB1 FamilyB1"
   "The FirstB of FamilyB"
   "FirstB PseudonymB"
   "Bee"
   "Effy Bee")
  nil
  nil
  nil
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstB FamilyB")


(bbdb-vcard-import-test
 "
** Additional ORGs go to Notes, org.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyC;FirstC
ORG:OrgC1
ORG:OrgC2
END:vcard
"
 ["FirstC" "FamilyC"
  nil
  "OrgC1"
  nil
  nil
  nil
  ((org . "OrgC2")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstC FamilyC")


(bbdb-vcard-import-test
 "
*** ... but only if they are unique
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyC;FirstC
ORG:OrgC1
ORG:OrgC2
ORG:OrgC3
ORG:OrgC3
ORG:OrgC4
END:VCARD
"
 ["FirstC" "FamilyC"
  nil
  "OrgC1"
  nil
  nil
  nil
  ((org . "OrgC4")
   (org . "OrgC3")
   (org . "OrgC2")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstC FamilyC")


(bbdb-vcard-import-test
 "
** Prefixes are discarded.
------------------------------------------------------------
X.BEGIN:VCARD
X.VERSION:3.0
X.N:FamilyD;FirstD
X.ORG:OrgD;UnitD
X.EMAIL:userD@hostD.example.com
X.END:VCARD
"
 ["FirstD" "FamilyD"
  nil
  "OrgD
UnitD"
  nil
  nil
  ("userD@hostD.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstD FamilyD")


(bbdb-vcard-import-test
 "
*** Same as before, don't change anything.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyD;FirstD
ORG:OrgD;UnitD
EMAIL:userD@hostD.example.com
END:VCARD
"
 ["FirstD" "FamilyD"
  nil
  "OrgD
UnitD"
  nil
  nil
  ("userD@hostD.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstD FamilyD")


(bbdb-vcard-import-test
 "
*** Same as before, don't change anything.
------------------------------------------------------------
Y.BEGIN:VCARD
Y.VERSION:3.0
Y.N:FamilyD;FirstD
Y.ORG:OrgD;UnitD
Y.EMAIL:userD@hostD.example.com
Y.END:VCARD
"
 ["FirstD" "FamilyD"
  nil
  "OrgD
UnitD"
  nil
  nil
  ("userD@hostD.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstD FamilyD")


(bbdb-vcard-import-test
 "
** Case Insensitivity
------------------------------------------------------------
BEGIN:Vcard
Version:3.0
n:FamilyE;FirstE
Org:OrgE;UnitE
email:userE@hostE.example.com
end:vcard
"
 ["FirstE" "FamilyE"
  nil
  "OrgE
UnitE"
  nil
  nil
  ("userE@hostE.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstE FamilyE")


(bbdb-vcard-import-test
 "
** Non-ASCII Content
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:Franz Rübezahl
N:Rübezahl;Franz
NICKNAME:Fränzchen,Rübe
ADR:Postschließfach 17;Zimmer Zwölf;Einbahnstraße;Ödstadt;;75480;
ORG:Rübe AG
END:VCARD
"
 ["Franz" "Rübezahl"
  ("Fränzchen" "Rübe")
  "Rübe AG"
  nil
  (["Office"
    ("Postschließfach 17" "Zimmer Zwölf" "Einbahnstraße")
    "Ödstadt"
    ""
    "75480"
    ""])
  nil
  ((creation-date . "2010-03-06") (timestamp . "2010-03-06")) ]
 "Rübe")


(bbdb-vcard-import-test
 "
*** Multiple, structured ADR
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyF;FirstF
ORG:OrgF;UnitF
ADR;TYPE=dom,home,postal,parcel:Box111,LHS;Room 111,or not;First Street,First Corner;Cityone;First State;11111,22222;Country
ADR;TYPE=intl,work,postal,parcel:Box222,RHS;Room 22,or something;Second Street,First Corner;Citytwo;Second State;222,33333;Country
ADR;TYPE=dom,work,postal,parcel:;;Second Street,First Corner;Citytwo;;222,33333;
ADR;TYPE=intl;TYPE=home;TYPE=parcel:;;Third Street,First Corner;Citythree;;222,33333;
END:VCARD
"
 ["FirstF" "FamilyF"
  nil
  "OrgF
UnitF"
  nil
  (["Home"
    ("Box111" "LHS" "Room 111" "or not" "First Street" "First Corner")
    "Cityone"
    "First State"
    "11111\n22222"
    "Country"]
   ["Office"
    ("Box222" "RHS" "Room 22" "or something" "Second Street" "First Corner")
    "Citytwo"
    "Second State"
    "222\n33333"
    "Country"]
   ["Office"
    ("Second Street" "First Corner")
    "Citytwo"
    ""
    "222\n33333"
    ""]
   ["Home"
    ("Third Street" "First Corner")
    "Citythree"
    ""
    "222\n33333"
    ""])
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstF FamilyF")


(bbdb-vcard-import-test
 "
*** Skip types from bbdb-vcard-skip-on-import
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyH;FirstH
ORG:OrgH;UnitH
EMAIL:userH@hostH.example.com
X-GSM-FOO:Blah
X-GSM-BAR:Blahblah
END:VCARD
"
 ["FirstH" "FamilyH"
  nil
  "OrgH
UnitH"
  nil
  nil
  ("userH@hostH.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstH FamilyH")


(bbdb-vcard-import-test
 "
*** Skip empty types.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyG;FirstG
ORG:OrgG;UnitG
EMAIL:userG@hostG.example.com
ROLE:
TITLE:
GEO:
END:VCARD
"
 ["FirstG" "FamilyG"
  nil
  "OrgG
UnitG"
  nil
  nil
  ("userG@hostG.example.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstG FamilyG")


(bbdb-vcard-import-test
 "
*** Remove X-BBDB- prefixes
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyN;FirstN
ORG:OrgN;UnitN
EMAIL:userN@hostN.example.com
X-BBDB-MARK-CHAR:b
X-BBDB-TEX-NAME:{\\\\em FirstM FamilyM}
END:VCARD
"
 ["FirstN" "FamilyN"
  nil
  "OrgN
UnitN"
  nil
  nil
  ("userN@hostN.example.com")
  ((tex-name . "{\\em FirstM FamilyM}")
   (mark-char . "b")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstN FamilyN")


(bbdb-vcard-import-test
 "
** Merging of vcard NOTEs
*** A vcard with two NOTEs.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyI;FirstI
ORG:OrgI
NOTE:Note No. 1a
NOTE:Note No. 1b
END:VCARD
"
 ["FirstI" "FamilyI"
  nil
  "OrgI"
  nil
  nil
  nil
  ((notes . "Note No. 1a;\nNote No. 1b")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstI FamilyI")


(bbdb-vcard-import-test
 "
*** Same as before, but a different NOTE.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyI;FirstI
ORG:OrgI
NOTE:Note No. 2
END:VCARD
"
 ["FirstI" "FamilyI"
  nil
  "OrgI"
  nil
  nil
  nil
  ((notes . "Note No. 1a;\nNote No. 1b;\nNote No. 2")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstI FamilyI")


(bbdb-vcard-import-test
 "
*** Same as before, but a NOTE we've seen already
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyI;FirstI
ORG:OrgI
NOTE:Note No. 1b
END:VCARD
"
 ["FirstI" "FamilyI"
  nil
  "OrgI"
  nil
  nil
  nil
  ((notes . "Note No. 1a;\nNote No. 1b;\nNote No. 2")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstI FamilyI")



(bbdb-vcard-import-test
 "
** Merging of vcard CATEGORIES
*** A vcard with two CATEGORIES.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyM;FirstM
ORG:OrgI
CATEGORIES:Category 1a,Category 1b
CATEGORIES:Category 2a,Category 2b
END:VCARD
"
 ["FirstM" "FamilyM"
  nil
  "OrgI"
  nil
  nil
  nil
  ((mail-alias . "Category 1a,Category 1b,Category 2a,Category 2b")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstM FamilyM")


(bbdb-vcard-import-test
 "
*** Same as before, but a different CATEGORIES.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyM;FirstM
ORG:OrgI
CATEGORIES:Category 3
END:VCARD
"
 ["FirstM" "FamilyM"
  nil
  "OrgI"
  nil
  nil
  nil
  ((mail-alias . "Category 1a,Category 1b,Category 2a,Category 2b,Category 3")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstM FamilyM")


(bbdb-vcard-import-test
 "
*** Same as before, but a CATEGORIES we've seen already
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyM;FirstM
ORG:OrgI
CATEGORIES:Category 2b
END:VCARD
"
 ["FirstM" "FamilyM"
  nil
  "OrgI"
  nil
  nil
  nil
  ((mail-alias . "Category 1a,Category 1b,Category 2a,Category 2b,Category 3")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstM FamilyM")


(bbdb-vcard-import-test
 "
** A vcard with two other vcards inside; we check the outer one
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:OuterfirstA OuterlastA
N:OuterlastA OuterfirstA
AGENT:BEGIN:VCARD\\nVERSION:3.0\\nN:InnerlastA\\;InnerfirstA\\nFN:InnerfirstA InnerlastA\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerA@hostA.com\\nEND:VCARD\\n
B.AGENT:BEGIN:VCARD\\nVERSION:3.0\\nN:InnerlastB\\;InnerfirstB\\nFN:InnerfirstB InnerlastB\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerB@hostB.com\\nEND:VCARD\\n
NOTE:A note
END:VCARD
"
 ["OuterlastA" "OuterfirstA"
  ("OuterfirstA OuterlastA")
  nil
  nil
  nil
  nil
  ((b\.agent . "BEGIN:VCARD
VERSION:3.0
N:InnerlastB;InnerfirstB
FN:InnerfirstB InnerlastB
TEL:+1-919-555-1234
EMAIL;TYPE=INTERNET:InnerB@hostB.com
END:VCARD
")
   (agent . "BEGIN:VCARD
VERSION:3.0
N:InnerlastA;InnerfirstA
FN:InnerfirstA InnerlastA
TEL:+1-919-555-1234
EMAIL;TYPE=INTERNET:InnerA@hostA.com
END:VCARD
")
   (notes . "A note")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "OuterfirstA OuterlastA")


(bbdb-vcard-import-test
 "
** A vcard with two other vcards inside; we check the first inner one
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:OuterfirstA OuterlastA
N:OuterlastA OuterfirstA
AGENT:BEGIN:VCARD\\nVERSION:3.0\\nN:InnerlastA\\;InnerfirstA\\nFN:InnerfirstA InnerlastA\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerA@hostA.com\\nEND:VCARD\\n
B.AGENT:BEGIN:VCARD\\nVERSION:3.0\\nN:InnerlastB\\;InnerfirstB\\nFN:InnerfirstB InnerlastB\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerB@hostB.com\\nEND:VCARD\\n
NOTE:A note
END:VCARD
"
 ["InnerfirstA" "InnerlastA"
  nil
  nil
  (["Office" "+1-919-555-1234"])
  nil
  ("InnerA@hostA.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "InnerfirstA InnerlastA")


(bbdb-vcard-import-test
 "
** A vcard with two other vcards inside; we check the second inner one
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
FN:OuterfirstA OuterlastA
N:OuterlastA OuterfirstA
AGENT:BEGIN:VCARD\\nVERSION:3.0\\nN:InnerlastA\\;InnerfirstA\\nFN:InnerfirstA InnerlastA\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerA@hostA.com\\nEND:VCARD\\n
B.AGENT:BEGIN:VCARD\\nVERSION:3.0\\nN:InnerlastB\\;InnerfirstB\\nFN:InnerfirstB InnerlastB\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerB@hostB.com\\nEND:VCARD\\n
NOTE:A note
END:VCARD
"
 ["InnerfirstB" "InnerlastB"
  nil
  nil
  (["Office" "+1-919-555-1234"])
  nil
  ("InnerB@hostB.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "InnerfirstB InnerlastB")


(bbdb-vcard-import-test
 "
** Treatment of REV
*** Store REV as creation-date in new records...
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyJ;FirstJ
ORG:OrgJ
REV:1997-03-27T22:27:10Z
END:VCARD
"
 ["FirstJ" "FamilyJ"
  nil
  "OrgJ"
  nil
  nil
  nil
  ((creation-date . "1997-03-27T22:27:10Z") (timestamp . "2010-03-04")) ]
 "FirstJ FamilyJ"
 nil nil t)


(bbdb-vcard-import-test
 "
*** ...but not in existing records
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyJ;FirstJ
ORG:OrgJ
REV:1977-12-03T22:27:10Z
END:VCARD
"
 ["FirstJ" "FamilyJ"
  nil
  "OrgJ"
  nil
  nil
  nil
  ((creation-date . "1997-03-27T22:27:10Z") (timestamp . "2010-03-04")) ]
 "FirstJ FamilyJ"
 nil nil t)


(bbdb-vcard-import-test
 "
*** The same, but dashless REV
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyR;FirstR
ORG:OrgR
REV:19771203T222710Z
END:VCARD
"
 ["FirstR" "FamilyR"
  nil
  "OrgR"
  nil
  nil
  nil
  ((creation-date . "1977-12-03T22:27:10Z") (timestamp . "2010-03-04")) ]
 "FirstR FamilyR"
 nil nil t)



(bbdb-vcard-import-test
 "
** Matching BDAY and N induce merge
*** Storing a new person
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyK;FirstK
ORG:CompanyK
BDAY:1927-03-27
END:VCARD
"
 ["FirstK" "FamilyK"
  nil
  "CompanyK"
  nil
  nil
  nil
  ((anniversary . "1927-03-27 birthday")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstK FamilyK")


(bbdb-vcard-import-test
 "
*** Not quite the same person: BDAY differs.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyK;FirstK
ORG:CompanyK2
BDAY:1937-04-28
END:VCARD
"
 ["FirstK" "FamilyK"
  nil
  "CompanyK2"
  nil
  nil
  nil
  ((anniversary . "1937-04-28 birthday")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstK FamilyK"
 "CompanyK2")


(bbdb-vcard-import-test
 "
*** Known person due to matching BDAY. Different ORG, though.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyK;FirstK
ORG:CompanyK1
BDAY:1927-03-27
END:VCARD
"
 ["FirstK" "FamilyK"
  nil
  "CompanyK1"
  nil
  nil
  nil
  ((anniversary . "1927-03-27 birthday")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstK FamilyK"
 "CompanyK1")


(bbdb-vcard-import-test
 "
*** Known person due to matching BDAY (albeit in another date format). Different ORG, again.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyK;FirstK
ORG:CompanyK3
BDAY:19270327
END:VCARD
"
 ["FirstK" "FamilyK"
  nil
  "CompanyK3"
  nil
  nil
  nil
  ((anniversary . "1927-03-27 birthday")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04")) ]
 "FirstK FamilyK"
 "CompanyK3")



(bbdb-vcard-import-test
 "
*** Anniversaries
** Birthdays include time.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyP;FirstP
BDAY:1927-03-27T23:44:54Z
END:VCARD
"
 ["FirstP" "FamilyP"
  nil
  nil
  nil
  nil
  nil
  ((anniversary . "1927-03-27T23:44:54Z birthday")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstP FamilyP")


(bbdb-vcard-import-test
 "
** Birthdays include time (half-obsolete format).
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyQ;FirstQ
BDAY:19580327T234454
END:VCARD
"
 ["FirstQ" "FamilyQ"
  nil
  nil
  nil
  nil
  nil
  ((anniversary . "1958-03-27T23:44:54 birthday")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstQ FamilyQ")


(bbdb-vcard-import-test
 "
** Non-birthday anniversaries
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyM;FirstM
BDAY:1927-03-27
X-BBDB-ANNIVERSARY:1960-12-12 wedding\\n1970-11-11 blah\\n1998-03-12 %s created bbdb-anniv.el %d years ago
END:VCARD
"
 ["FirstM" "FamilyM"
  nil
  nil
  nil
  nil
  nil
  ((anniversary . "1927-03-27 birthday\n1960-12-12 wedding\n1970-11-11 blah\n1998-03-12 %s created bbdb-anniv.el %d years ago")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstM FamilyM")


(bbdb-vcard-import-test
 "
** Non-birthday anniversaries, no BDAY
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyN;FirstN
X-BBDB-ANNIVERSARY:1960-12-12 wedding\\n1970-11-11 blah
END:VCARD
"
 ["FirstN" "FamilyN"
  nil
  nil
  nil
  nil
  nil
  ((anniversary . "1960-12-12 wedding\n1970-11-11 blah")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstN FamilyN")



(bbdb-vcard-import-test
 "
** No BDAY, but unlabelled birthday in anniversary
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyO;FirstO
X-BBDB-ANNIVERSARY:1960-12-12\\n1970-11-11 blah
NOTE:On re-import, birthday gets labelled.
   Therefore, re-import test of this one should fail.
END:VCARD
"
 ["FirstO" "FamilyO"
  nil
  nil
  nil
  nil
  nil
  ((anniversary . "1960-12-12\n1970-11-11 blah")
   (notes . "On re-import, birthday gets labelled.  Therefore, re-import test of this one should fail.")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstO FamilyO")



(bbdb-vcard-import-test
 "
** Matching TEL and N induce merge
*** Storing a new person
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyL;FirstL
TEL;TYPE=work:111100001
TEL;TYPE=home:111100002
TEL:111100003
ORG:CompanyL
END:VCARD
"
 ["FirstL" "FamilyL"
  nil
  "CompanyL"
  (["Office" "111100001"]
   ["Home" "111100002"]
   ["Office" "111100003"]
)
  nil
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstL FamilyL")


(bbdb-vcard-import-test
 "
*** Not quite the same person: no matching TEL.
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyL;FirstL
TEL;TYPE=work:222200001
TEL;TYPE=home:222200002
TEL:222200003
ORG:CompanyL2
END:VCARD
"
 ["FirstL" "FamilyL"
  nil
  "CompanyL2"
  (["Office" "222200001"]
   ["Home" "222200002"]
   ["Office" "222200003"])
  nil
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstL FamilyL"
 "CompanyL2")


(bbdb-vcard-import-test
 "
*** Known person: matching TEL (but different ORG).
------------------------------------------------------------
BEGIN:VCARD
VERSION:3.0
N:FamilyL;FirstL
TEL;TYPE=work:333300001
TEL;TYPE=work:111100002
TEL:333300003
ORG:CompanyL3
END:VCARD
"
 ["FirstL" "FamilyL"
  nil
  "CompanyL3"
   (["Office" "111100003"]
    ["Home" "111100002"]
    ["Office" "111100001"]
    ["Office" "333300001"]
    ["Office" "111100002"]
    ["Office" "333300003"])
  nil
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "FirstL FamilyL"
 "CompanyL3")



(bbdb-vcard-import-test
 "
** From RFC 2426: author's address.  Note the omission or type N
   which is declared mandatory by this very RFC.
------------------------------------------------------------
BEGIN:vCard
VERSION:3.0
FN:Frank Dawson
ORG:Lotus Development Corporation
ADR;TYPE=WORK,POSTAL,PARCEL:;;6544 Battleford Drive
 ;Raleigh;NC;27613-3502;U.S.A.
TEL;TYPE=VOICE,MSG,WORK:+1-919-676-9515
TEL;TYPE=FAX,WORK:+1-919-676-9564
EMAIL;TYPE=INTERNET,PREF:Frank_Dawson@Lotus.com
EMAIL;TYPE=INTERNET:fdawson@earthlink.net
URL:http://home.earthlink.net/~fdawson
END:vCard
"
 ["" ""
  ("Frank Dawson")
  "Lotus Development Corporation"
  (["Office" "+1-919-676-9515"] ["Office" "+1-919-676-9564"])
  (["Office"
    ("6544 Battleford Drive")
    "Raleigh"
    "NC"
    "27613-3502"
    "U.S.A."])
  ("Frank_Dawson@Lotus.com" "fdawson@earthlink.net")
  ((www . "http://home.earthlink.net/~fdawson")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "Frank Dawson")

(bbdb-vcard-import-test
 "
** The other author of RFC 2426
------------------------------------------------------------
BEGIN:vCard
VERSION:3.0
FN:Tim Howes
ORG:Netscape Communications Corp.
ADR;TYPE=WORK:;;501 E. Middlefield Rd.;Mountain View;
 CA; 94043;U.S.A.
TEL;TYPE=VOICE,MSG,WORK:+1-415-937-3419
TEL;TYPE=FAX,WORK:+1-415-528-4164
EMAIL;TYPE=INTERNET:howes@netscape.com
END:vCard
"
 ["" ""
  ("Tim Howes")
  "Netscape Communications Corp."
  (["Office" "+1-415-937-3419"]
   ["Office" "+1-415-528-4164"])
  (["Office"
    ("501 E. Middlefield Rd.")
    "Mountain View"
    "CA"
    " 94043"
    "U.S.A."])
  ("howes@netscape.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "Tim Howes")



(bbdb-vcard-import-test
 "
** vCard version 2.1
------------------------------------------------------------
BEGIN:VCARD
VERSION:2.1
N:Friday;Fred
TEL;WORK;VOICE:+1-213-555-1234
TEL;WORK;FAX:+1-213-555-5678
BDAY:19661221t173745
END:VCARD
"
 ["Fred" "Friday"
  nil
  nil
  (["Office" "+1-213-555-1234"]
   ["Office" "+1-213-555-5678"])
  nil
  nil
  ((anniversary . "1966-12-21T17:37:45 birthday") (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "Fred Friday")


(bbdb-vcard-import-test
 "
** vCard version 2.1
*** Case insensitivity
------------------------------------------------------------
begin:VCARD
version:2.1
n:Thursday;Tom
tel;WORK;VOICE:+1-213-555-1234
tel;WORK;FAX:+1-213-555-5678
end:VCARD
"
 ["Tom" "Thursday"
  nil
  nil
  (["Office" "+1-213-555-1234"]
   ["Office" "+1-213-555-5678"])
  nil
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "Tom Thursday")


(bbdb-vcard-import-test
 "
** vCard version 2.1
------------------------------------------------------------
BEGIN:VCARD
VERSION:2.1
N:Smith;John;M.;Mr.;Esq.
TEL;WORK;VOICE;MSG:+1 (919) 555-1234
TEL;CELL:+1 (919) 554-6758
TEL;WORK;FAX:+1 (919) 555-9876
ADR;WORK;PARCEL;POSTAL;DOM:Suite 101;1 Central St.;AnyTown;NC;27654
END:VCARD
"
 ["Mr. John M." "Smith Esq."
  nil
  nil
  (["Office" "+1 (919) 555-1234"]
   ["Mobile" "+1 (919) 554-6758"]
   ["Office" "+1 (919) 555-9876"])
  (["Office" ("Suite 101" "1 Central St." "AnyTown") "NC" "27654" "" ""])
  nil
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
  "Smith")


(bbdb-vcard-import-test
 "
** vCard version 2.1
*** Quoted-printable
------------------------------------------------------------
BEGIN:VCARD
VERSION:2.1
N:Doe;John;;;
FN:John Doe
ORG:Doe Company, The;
TITLE: President
NOTE;ENCODING=QUOTED-PRINTABLE: This is a note associated
  with this contact=0D=0A
TEL;WORK;VOICE:(987) 123-4567
TEL;HOME;VOICE:(987) 765-4321
TEL;CELL;VOICE:(987) 135-8642
TEL;WORK;FAX:(987) 246-1357
ADR;WORK:;;1234 North Street;Anytown;TX 751234;;United States
  of America
LABEL;WORK;ENCODING=QUOTED-PRINTABLE:1234 North Street=0D=0AAnytown,
  TX 751234 =0D=0AUnited States of America
URL:
URL:<WWLINK TYPE=\"GENERIC\"
 VALUE=\"http://www.doeweb.com\">http://www.doeweb.com</WWLINK>
EMAIL;PREF;INTERNET:jdoe@nowhere.com
REV:19980114T170559Z
END:VCARD
"
 ["John" "Doe"
  nil
  "Doe Company, The
"
  (["Office" "(987) 123-4567"]
   ["Home" "(987) 765-4321"]
   ["Mobile" "(987) 135-8642"]
   ["Office" "(987) 246-1357"])
  (["Office" ("1234 North Street") "Anytown" "TX 751234" "" "United States of America"])
  ("jdoe@nowhere.com")
  ((label\;type=work . "1234 North Street
Anytown, TX 751234 
United States of America")
   (title . "President")
   (notes . "This is a note associated with this contact
")
   (www . "http://www.doeweb.com")
   (creation-date . "1998-01-14T17:05:59Z") (timestamp . "2010-03-04"))]
 "John Doe"
 nil nil t)



(bbdb-vcard-import-test
 "
** A v2.1 vcard with another vcard inside; we check the outer one
------------------------------------------------------------
BEGIN:VCARD
VERSION:2.1
N:Outerlast2A; Outerfirst2A
FN:Outerfirst2A Outerlast2A
AGENT:BEGIN:VCARD\\nVERSION:2.1\\nN:Innerlast2A\\;Innerfirst2A\\nFN:Innerfirst2A Innerlast2A\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerA@hostA.com\\nEND:VCARD\\n
NOTE:A note
END:VCARD
"
 [" Outerfirst2A" "Outerlast2A"
  ("Outerfirst2A Outerlast2A")
  nil
  nil
  nil
  nil
  ((agent . "BEGIN:VCARD\\
VERSION:2.1\\
N:Innerlast2A\\;Innerfirst2A\\
FN:Innerfirst2A Innerlast2A\\
TEL:+1-919-555-1234\\
EMAIL\\;TYPE=INTERNET:InnerA@hostA.com\\
END:VCARD\\
")
   (notes . "A note")
   (creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "Outerfirst2A Outerlast2A")


(bbdb-vcard-import-test
 "
** A v2.1 vcard with another vcard inside; we check the inner one
------------------------------------------------------------
BEGIN:VCARD
VERSION:2.1
N:Outerlast2A Outerfirst2A
AGENT:BEGIN:VCARD\\nVERSION:2.1\\nN:Innerlast2A\\;Innerfirst2A\\nFN:Innerfirst2A Innerlast2A\\nTEL:+1-919-555-
 1234\\nEMAIL\\;TYPE=INTERNET:InnerA@hostA.com\\nEND:VCARD\\n
NOTE:A note
END:VCARD
"
 ["Innerfirst2A" "Innerlast2A"
  nil
  nil
  (["Office" "+1-919-555-1234"])
  nil
  ("InnerA@hostA.com")
  ((creation-date . "2010-03-04") (timestamp . "2010-03-04"))]
 "Innerfirst2A Innerlast2A")



;;;; The Export/Re-Import Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(bbdb "" nil)
(with-current-buffer "*BBDB*"
  (bbdb-vcard-export "/tmp/test-bbdb-0.vcf" t nil))

(let ((first-bbdb (bbdb-search (bbdb-records) ""))
      second-bbdb)
  (bbdb-save-db)
  (save-buffer bbdb-buffer)
  (kill-buffer bbdb-buffer)
  (kill-buffer "*BBDB*")
  (delete-file "/tmp/test-bbdb")
  (bbdb-vcard-import-file "/tmp/test-bbdb-0.vcf")
  (setq second-bbdb (bbdb-search (bbdb-records) ""))
  (bbdb-vcard-compare-bbdbs first-bbdb second-bbdb))
;; FIXME: previous line messes bbdb up.

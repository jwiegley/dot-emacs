<?php  
  require('functions.php3');
  small_header("Previous Releases of Proof General"); 
  ?>

<p>
Please note that we do not support these old releases in any way.
</p>

<h2>Proof General Version 3.3, released  10th September 2001</h2>
<p>
This version of Proof General has been tested
with XEmacs 21.4 and (briefly) with GNU Emacs 20.7
(it does <b>not</b> support GNU Emacs 21.x).
It supports Coq version 7.x, LEGO version 1.3.1 and
Isabelle2002.
</p>

<ul>
  <li> gzip'ed tar file: 
      <?php download_link("ProofGeneral-3.3.tar.gz") ?>,
      <br>
      or the same thing in a zip file:
      <?php download_link("ProofGeneral-3.3.zip") ?>,
  </li>
 <li> Linux RPM package:
      <?php download_link("ProofGeneral-3.2-1.noarch.rpm") ?>
 </li>
</ul>
<p>
Check the <?php fileshow("ProofGeneral-3.3/CHANGES","CHANGES"); ?> file
for a summary of changes since version 3.2.
</p>


<h2>Proof General Version 3.2, released 2nd October 2000</h2>
<p>
This version of Proof General has been tested
with XEmacs 21.1 and (briefly) with GNU Emacs 20.7.
It supports Coq version 6.3, LEGO version 1.3.1 and
Isabelle99-1.
</p>

<ul>
  <li> gzip'ed tar file: 
      <?php download_link("ProofGeneral-3.2.tar.gz") ?>,
      <br>
      or the same thing in a zip file:
      <?php download_link("ProofGeneral-3.2.zip") ?>,
  </li>
 <li> Linux RPM package:
      <?php download_link("ProofGeneral-3.2-1.noarch.rpm") ?>
     <br>
     Also a
      <?php download_link("ProofGeneral-3.2-1.src.rpm",
	"source RPM") ?>.
 </li>
</ul>
<p>
Check the <?php fileshow("ProofGeneral-3.2/CHANGES","CHANGES"); ?> file
for a summary of changes since version 3.1.
</p>

<h2>Proof General Version 3.1, released 23rd March 2000</h2>

<p>
This version of Proof General has been tested
with XEmacs 21.1 and GNU Emacs 20.4.
It supports Coq version 6.3, LEGO version 1.3.1 and
Isabelle99.
</p>

<ul>
  <li> gzip'ed tar file: 
      <?php download_link("ProofGeneral-3.1.tar.gz") ?>
       <br>or zip file:
      <?php download_link("ProofGeneral-3.1.zip") ?>,
  </li>
  <li> RPM package:
      <?php download_link("ProofGeneral-3.1-1.noarch.rpm") ?>
     <br>
     The 
      <?php download_link("ProofGeneral-3.1-1.src.rpm",
	"source RPM") ?>.
   </li>
</ul>
<p>
Check the <?php fileshow("ProofGeneral-3.1/CHANGES","CHANGES"); ?> file
for a summary of changes since version 3.0.
</p>



<h2>Proof General Version 3.0, released 26th November 1999</h2>

<p>
This version of Proof General has been tested
with XEmacs 20.4, XEmacs 21.1.8 and GNU Emacs 20.5.<br>
It supports Coq version 6.3, LEGO version 1.3.1 and Isabelle99.
</p>
<ul>
  <li> gzip'ed tar file: 
      <?php download_link("ProofGeneral-3.0.tar.gz") ?>
  </li>
 <li> Linux RPM package:
      <?php download_link("ProofGeneral-3.0-1.noarch.rpm") ?>
     <br>
     The source RPM is 
      <?php download_link("ProofGeneral-3.0-1.noarch.rpm","here") ?>.
 </li>
</ul>
<p>
Check the <?php fileshow("ProofGeneral-3.0/CHANGES","CHANGES"); ?> file
for a summary of changes since version 2.1.
</p>



<h2>Proof General Version 2.1, released 24th August 1999</h2>

<p>
This version of Proof General has been tested
with XEmacs 20.4, XEmacs 21 and GNU Emacs 20.3.<br>
It supports Coq version 6.3, LEGO version 1.3.1 and
some pre-release versions of Isabelle version 99.
<ul>
  <li> gzip'ed tar file: 
      <?php download_link("ProofGeneral-2.1.tar.gz") ?>
  </li>
 <li> Linux RPM package:
      <?php download_link("ProofGeneral-2.1-1.noarch.rpm") ?>
     <br>
     The source RPM is 
      <?php download_link("ProofGeneral-2.1-1.noarch.rpm","here") ?>.
 </li>
</ul>


<h2>Proof General Version 2.0, released 16th December 1998</h2>

<p>
This version of Proof General has been tested
with XEmacs 20.4 and GNU Emacs 20.2, 20.3.<br>
It supports Coq version 6.2, LEGO version 1.3.1, and
Isabelle version 98-1.<br>
</p>
<ul>
  <li> gzip'ed tar file: 
      <?php download_link("ProofGeneral-2.0.tar.gz") ?>
  </li>
 <li> Linux RPM package:
      <?php download_link("ProofGeneral-2.0-1.noarch.rpm") ?>
     <br>
     The source RPM is 
      <?php download_link("ProofGeneral-2.0-1.noarch.rpm","here") ?>.
 </li>
</ul>

<?php
   click_to_go_back();
   footer();
?>

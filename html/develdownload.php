<!-- -*- html -*- -->
<?php  
  require('functions.php3');
  small_header("Proof General Development Release"); 
  ?>


<p>
<a href="#prerel">Below</a> is the latest pre-release of Proof General,
made available for those who wish to test the latest features or bug
fixes.  For developers, this release is also available as a 
<a href="#devel">complete CVS snapshot</a> (further below), which
includes files not needed for the running program.
</p>
<p>
Pre-releases of Proof General may be buggy as we add new features and
experiment with them.  Nonetheless, we welcome bug reports.  But
please make sure you are using the latest pre-release before
reporting problems.
</p>
<p>
Please <a href="register">register</a> if you haven't done so already.
</p>


<!-- WARNING!  Line below automatically edited by makefile. -->
<h2><a name="doc">Manual for ProofGeneral-3.4pre020807</a></h2>
<!-- End Warning. -->
<p>
The manual included with the pre-release may be
updated from that of the 
<a href="doc">last stable release</a>.
</p>
<p>
Here is the pre-release documentation: the user manual in
<?php htmlshow("ProofGeneral-latest/doc/ProofGeneral_toc.html","HTML","Proof General manual") ?>,
<?php download_link("ProofGeneral-latest/doc/ProofGeneral.ps.gz", "ps") ?> 
or  
<?php download_link("ProofGeneral-latest/doc/ProofGeneral.pdf", "pdf") ?>,
and the new separate "adapting" manual, in
<?php htmlshow("ProofGeneral-latest/doc/PG-adapting_toc.html","HTML","Adapting Proof General manual") ?>,
<?php download_link("ProofGeneral-latest/doc/PG-adapting.ps.gz", "ps") ?> 
or  
<?php download_link("ProofGeneral-latest/doc/PG-adapting.pdf", "pdf") ?>.
</p>


<!-- WARNING!  Line below automatically edited by makefile. -->
<h2><a name="prerel">Pre-release: ProofGeneral-3.4pre020807</a></h2>

<p> 
Check the 
<!-- WARNING!  Line below automatically edited by makefile. --> 
<?php fileshow("ProofGeneral-3.4pre020807/CHANGES","CHANGES"); ?> file 
<!-- End Warning. --> 
for a summary of changes since the last stable
version, and notes about work-in-progress.  </p> 
<table width="80%" cellspacing=8> 
<tr><td width=150>gzip'ed tar file</td>
<!-- WARNING!  Lines below automatically edited by makefile. -->
<td><?php download_link("ProofGeneral-3.4pre020807.tar.gz") ?></td>
</tr>
<tr>
<td>zip file</td>
<td><?php download_link("ProofGeneral-3.4pre020807.zip") ?></td>
</tr>
<tr>
<td>RPM package </td>
<td><?php download_link("ProofGeneral-3.4pre020807-1.noarch.rpm") ?></td>
</tr>
<tr>
<td>individual files</td>
<td><a href="ProofGeneral">http access to files in development release</a>
</tr>
</table>
<p>
NB: we no longer distribute the source RPM, since you can build
both source and  "binary" RPMs direct from the tarball using
"rpm -ta".
</p>
<!-- End Warning. -->
<p> 
<b>Emacs versions:</b>
This version has been tested with XEmacs version 21.4.8 and with GNU
Emacs 21.2.1.  XEmacs support is better tested.  Older releases of Emacs
<i>may</i> work, but we recommend the use of these or newer versions
because backwards compatibility across different Emacs versions is too
difficult to support.  If you cannot upgrade your Emacs, consider
using an <a href="oldrel.php">older release</a> of Proof General.
</p> 
<p>
<b>Prover versions:</b>
This version has been tested with Coq 7.3, Isabelle2002, Lego 1.3.1,
and PhoX 0.8.
</p>
<p>
For install instructions, see 
the <a href="download#install">stable version download</a>.
</p>

<p>
</p>
<p>
</p>


<!-- WARNING!  Line below automatically edited by makefile. -->
<h2><a name="devel">Complete archive of ProofGeneral-3.4pre020807 for developers</a></h2>
<!-- End Warning. -->

<p>
This archive is a snapshot from our CVS repository. 
</p>
<ul>
  <li> gzip'ed tar file: 
<!-- WARNING!  Line below automatically edited by makefile. -->
      <?php download_link("ProofGeneral-3.4pre020807-devel.tar.gz") ?>
<!-- End Warning. -->
  </li>
</ul>
<p>
What's the difference from the user's pre-release above?
The complete archive also includes:
</p>
<ul>
  <li> the low-level developer's todo files 
    (see <a href="devel#lowleveltodo">the developers page</a>)
   and the detailed
   <!-- WARNING!  Line below automatically edited by makefile. -->
   <?php fileshow("ProofGeneral-3.4pre020807/ChangeLog","ChangeLog"); ?>,
   <!-- End Warning. -->
 </li>
  <li> developer's Makefile used to generate documentation files 
       and the release itself,</li>
  <li> test files, </li>
  <li> image source files, </li>
  <li> the web pages, </li>
  <li> working instantiations of Proof General for new provers </li>
</ul>
<p>
Most people don't need this.  Note that there are no pre-built
documentation files in the developer's release (developers can
run Make, by definition).
</p>

<?php
   click_to_go_back();
   footer();
?>

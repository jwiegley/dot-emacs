<?php  
  require('functions.php3');
  small_header("Proof General Kit"); 
  ?>

<p>
The Proof General Kit project is in an early experimental stage at
the moment.  If you are interested in collaborating, or have ideas
or suggestions to contribute, please send a note to
<a href="mailto:da+pg-kit@inf.ed.ac.uk"><tt>da+pg-kit@inf.ed.ac.uk</tt></a>
</p>

<h3>Planning</h3>
<p>
Ideas for the future of Proof General are described in these papers:
</p>
<ul>
<li><a href="http://homepages.inf.ed.ac.uk/da">David Aspinall</a>.
    <b><i>Protocols for Interactive e-Proof</i></b>.
    Draft version, see 
    <a href="http://homepages.inf.ed.ac.uk/da/papers/drafts/#eproof">here</a>.
</li>
<li><a href="http://homepages.inf.ed.ac.uk/da">David Aspinall</a>.
    <b><i>Proof General Kit (white paper)</i></b>.
    Draft version, see 
    <a href="http://homepages.inf.ed.ac.uk/da/papers/drafts/#white">here</a>.
</li>
</ul>

<h3>Development</h3>
<p>
Work which is currently in progress includes:
<ul>
 <li>The definition of PGIP and PGML, as 
     <a href="http://www.relaxng.org">RELAX NG</a> schemas.<br>
     Recent versions: 
      <?php download_link("Kit/dtd/pgip.rnc") ?>,
      <?php download_link("Kit/dtd/pgml.rnc") ?>.
     <br/>
     The derived DTDs are:
      <?php download_link("Kit/dtd/pgip.dtd") ?>,
      <?php download_link("Kit/dtd/pgml.dtd") ?>.
     <br/>
     There is also a <b>draft</b> commentary available,
      <?php download_link("Kit/docs/commentary.pdf") ?>.
     <br/>
     This updates the white paper mentioned above.

 </li>
 <li>Together with <a href="http://www.informatik.uni-bremen.de/~cxl/">Christoph Lüth</a>:
     a Haskell front-end and PGIP mediator, described in a
       <a href="http://www.informatik.uni-bremen.de/uitp03/">UITP '03</a>
       paper <a href="Kit/docs/uitp03.pdf">here</a>.
 <li>With assistance from Isabelle developers at Munich:
     a PGIP-enabled version of Isabelle/Isar
     (patch available soon).
 </li>
</ul>
</p>
<p>
We hope to make an alpha version of some software available in the
not-<em>too</em>-distant future. 
</p>

<?php
   click_to_go_back();
   footer();
?>

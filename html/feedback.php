<?php
##
##  Proof General feedback form.
##  
##  David Aspinall, June 1999.
##
##  $Id$
##
  require('functions.php3');

  if ($argv[0] !="submit"): 
###
### Feedback form
###
  small_header("Proof General Feedback Form"); 
?>

<p>
Please use the form below to send us comments, suggestions,
or offers to help with Proof General development.
Or simply send an email directly to
the <?php mlinktxt($project_feedback, "Proof General maintainer &lt;$project_feedback&gt."); ?>
</p>
<p>
You can also report a bug using this form, although it would
be more helpful to do this from within Emacs, using the 
"<kbd>Proof General -> Submit bug report</kbd>" menu command.
</p>

<form method=post action="<?php print $PHP_SELF . "?submit"; ?>">
<table width="450" border="0" cellspacing="2" cellpadding="0">
<tr>
  <td width="20%">From:</td>
  <td width="80%"><input type=text name="from" size="40"></td>
</tr>
<tr>
  <td>Subject:</td>
  <td><input type=text name="subject" size="40"></td>
</tr>
<tr><td colspan="2">
<textarea rows="15" cols="70" wrap="physical" name="feedback">
Dear Proof General developers,
</textarea>
(For us to reply, please include a proper email
 address in the From box).
</td></tr>
<tr><td></td><td>
<p align=right>
<input type=reset value="Clear">
<input type=submit value="Send feedback"> 
</p>
</td></tr>
</table>
</form>

<?php  
   click_to_go_back(); 
   footer(); 
  else:
##
##  Process feedback
##
   small_header("Thank-you!"); 
   
   /* NB: No validation of address! */

   /* FIXME: could append extra info to feedback. */

   $message = "From:\t\t" . $from . "\nSubject:\t" . $subject 
	   . "\n\n" . "Message:\n" . $feedback;

   if ($from != "") { print "<p>Dear " . $from . ",</p>\n"; };
   print "<p>";
   print "Thank-you for sending us feedback";
   if ($subject != "") { print " about " . $subject; };
   print ".</p>\n<p>";
   print "If you provided a valid return email address, somebody from the Proof General team will acknowledge your message after it has been read.";
   print "</p>";

   mail($project_feedback,  
	"[Web Feedback Form]: " . $subject,
	$message,
        "Reply-To: " . $from . "\n");

   click_to_go_back();
  
   footer();
endif;
?>

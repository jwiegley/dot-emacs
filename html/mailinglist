<?php  
/*
 *  Proof General mailing list subscription and unsubscription.
 *  
 *  David Aspinall, June 1999.
 *
 *  $Id$
 *
 */

  require('functions.php3');
  if ($subscribe == ""):
##
## Subscription form
##
  small_header("Proof General Mailing List"); 
  ?>
<p>
The mailing list address is 
<a href="mailto:users@proofgeneral.org">
<tt>users@proofgeneral.org</tt>.
</a>
</p>
  
<p>
To subscribe or unsubscribe, you can fill in the form below.
<br>
Or send a message to 
<a href="mailto:majordomo@proofgeneral.org">
 <tt>majordomo@proofgeneral.org</tt>
</a>
with the words "<tt>subscribe proofgeneral</tt>"
(or "<tt>unsubscribe proofgeneral"</tt>) in the message body.
</p>

<p>
Since its beginning, the mailing list has been a low-volume list (one
message every few months).  If the volume increases significantly due
to user interaction, we will introduce a separate mailing list for
announcements.  
</p>

<h2>Mailing list subscription</h2>

<form method=post action="<?php echo $PHP_SELF; ?>">
<table width="300" border="0" cellspacing="2" cellpadding="0">
<tr>
 <td width="30%">Your name:</td>
 <td width="70%"><input type=text name="name" size="40"></td>
</tr>
<tr>
 <td width="30%">Email address:</td>
 <td width="70%"><input type=text name="email" size="40"></td>
</tr>
<tr>
 <td width="30%"><input type=radio name="subscribe" value="yes" checked></td>
 <td width="70%">Please add me to the mailing list.</td>
</tr>
<tr>
 <td width="30%"><input type=radio name="subscribe" value="no"></td>
 <td width="70%">Please remove me from the mailing list.</td>
</tr>
</table>
<input type=submit value="Send request"> 
</form>
<p>
</p>
<?php  
  click_to_go_back();  
  footer(); 

  else:
##
##  Process subscription
##
   $title = ($subscribe == "yes" ? "Subscription" : "Unsubscription") . " Request";
   small_header($title);

   $request = ($subscribe == "yes" ? "join" : "be removed");
   
   $message = ($subscribe == "yes" ? "subscribe " : "unsubscribe ") 
		. "proofgeneral"; 
   mail("majordomo@dcs.ed.ac.uk",
	"[Web form from ~proofgen]",
	$message,
        "Reply-To: " . $email . "\nFrom: " . $email);

   if ($from != "") { print "<p>Dear " . $from . ",</p>\n"; };
   print "<p>";
   print "Your request to " . $request . " the proof general mailing list has been submitted.<br>";
   print "Thank-you!";
   print "</p>\n<p>";

   click_to_go_back();
  
   footer();
 endif;
?>


<?php
//
// Dave's PHP Header
//
// Included in every page.  
// Prints DTD, <html> opening tag,
// and defines some useful functions.
//
// David Aspinall, June 1999/2002.
//
// $Id$
//
//


// Project configuration

$project_email = "feedback@proofgeneral.org";
$project_list  = "users@proofgeneral.org";
$project_feedback = "feedback@proofgeneral.org";

// Disable when free parking forwarding is broken
// $proofgenatdcs = "proofgen@dcs.ed.ac.uk";
// $project_email = $proofgenatdcs;
// $project_list  = $proofgenatdcs;
// $project_feedback = $proofgenatdcs;

$project_title = "Proof General";

$project_subtitle = "Organize your Proofs!";
$project_full_title = $project_title . " --- " . $project_subtitle;

if ($title == "") { $title = $project_title; }  // default page title.

///////////////////////////////////////////////////////////////////
//
// DTD 
//

$dtd_strict = "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n";
$dtd_loose = "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0 Transitional//EN\" \"http://www.w3.org/TR/REC-html40/loose.dtd\">\n";
$xml_header="<?xml version=\"1.0\"?>";
$dtd_xml_loose ="<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">";
$dtd_xml_strict ="<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">";
$html="<html>\n";
$xhtml="<html xmlns=\"http://www.w3.org/1999/xhtml\">\n";

print $dtd_loose;
print $html;

//print $xml_header;
//print $dtd_xml_strict;
//print $xhtml;


// Validator address

// $validator = "http://validator.dcs.ed.ac.uk/";
// It's a private link which won't work elsewhere, but never mind.
 $validator = "http://localhost/validator/";

function mlink($addr) {
  print "<a href=\"mailto:" . $addr . "\">" . $addr . "</a>";
}

function mlinktxt($addr,$txt) {
  print "<a href=\"mailto:" . $addr . "\">" . $txt . "</a>";
}


// FIXME: doesn't seem to work.  Why not?
function project_email() {
  mlink($project_email);
}


/* Style sheet element for dt doesnt work in Netscape 4, so hack it here.  
   NB!  This violates HTML 4 DTD.
*/
function dt($string,$name="") {
  print "<dt>";
  if ($name != "") { print "<a name =\"$name\">"; }
  print "<div style=\"font-style:italic; font-weight: bold\">";
  print $string;
  print "</div>";
  if ($name != "") { print "</a>"; }
  print "</dt>";
}

/* Automatic footnotes? */
/* FIXME: for now, just inline them. */

function footnote ($text) {
   print "<p><i><small>[" . $text . "]</small></i></p>";
}

/* A hyper-link with optional mouse over text.
   Could be made more sophisticated to do roll-overs, 
   or whatever.
*/

function hlink ($url,$text,$mouseover="") {
  print "<a href=\"" . $url . "\"";
  if ($mouseover != "") {
	print " onMouseOver=\"window.status='" . $mouseover . "'; return true;\"";
  };
  print ">" . $text . "</a>";
}

/* Determining download sizes (print broken message if file not found) */

function download_size($filename) {
   if (file_exists($filename)) {
	$size = filesize($filename);
        $sizek = (int) ($size/1024);
   	print " (";
   	if ($sizek == 0) {
	     print $size . " bytes)";
   	} else {
	     print $sizek . "k)";
   	}
   } else {
	print " (link broken)";
   }
}

function download_link($filename,$linkname = "") {
   print "<a href=\"" . $filename . "\">";
   if ($linkname == "") { 
	print $filename;
   } else {
	print $linkname;
   };
   print "</a>";
   print download_size($filename);
}

function date_modified($filename) {
   $time = filemtime($filename);
   if ($time) {
	print "Last modified " . strftime("%d %B %Y",$time) . ".\n";
   }
}

function small_header($title) {
  include('head.html');
  include('smallheader.html'); 
  print "<h1>" . $title . "</h1>\n</td>\n</table>\n";
}

function small_header_body($title) {
  include('smallheader.html'); 
  print "<h1>" . $title . "</h1>\n</td>\n</table>\n";
/*  print "<p>";  FIXME: hack to get CSS to work with bad HTML from texi2html */
}

/* FIXME: remove this function: maybe just set a global variable,
   or use SCRIPT_NAME, and then include footer.html. */

function footer($filemodified=".") {
  global $project_feedback;
  include('footer.html'); 
  date_modified($filemodified);
  print "</address>\n";
//  print "</font>\n";  /* Naughty stuff for older browsers, shouldn't do if V4 */
  print "</body>\n";
  print "</html>\n";
}

function click_to_go_back() {
  // FIXME: the empty href no longer refers to the root,
  // so this use of "/" breaks relative linking.
  print "<p>\nClick <a href=\"/\">here</a> to go back to the ";
  print $project_title; // FIXME: doesn't work, prints nothing.
  print " front page.</p>\n";
}

/* Link to a marked up file */
/* NB: could determine type automatically! */

function fileshow($filename,$text="",$title="") {
 if ( $text == "") { $text=$filename; };
 $message=$title;
 if ( $message == "") { $message=$filename; };
 $titlecode = ($title == "" ?  "" : "&title=" . urlencode($title));
 hlink("fileshow.php?file=" . urlencode($filename) . $titlecode,
	$text, $message);
}


/* Similar for html file (NB: could pick automatically) */

function htmlshow($filename,$text="",$title="") {
 if ( $text == "") { $text=$filename; };
 $message=$title;
 if ( $message == "") { $message=$filename; };
 $urlbits = parse_url($filename);
 hlink("htmlshow.php"
       . "?title=" . urlencode($title) 
       . "&file=" . urlencode($urlbits["path"])
       . ($urlbits["fragment"]=="" ? "" : "#" . $urlbits["fragment"]),
	$text, $message);
}




/* Markup plain text file, by escaping < and > */

function markup_plain_text($filename) {
  $file = file($filename);
  for($i = 0;$i < count($file);$i++) {
     $line = $file[$i];
     $line = ereg_replace("<","&lt;",$line);
     $line = ereg_replace(">","&gt;",$line);
     print $line;
  };
}

/* Hack an html file to be shown with our style sheet
   and hack relative links to go via htmlshow.php. 
   This isn't particularly robust, but seems to work for
   the output of texi2html.
*/

function hack_html($filename,$title="")  {
  if ($title=="") { $title=$filename; };
  $file = file($filename);
  /* Paste style sheet in head */
  for($i = 0;$i < count($file);$i++) {
     $line = $file[$i];
     if (eregi("</HEAD>",$line)) {
        /* Paste in style sheet */
	print "<style type=\"text/css\">\n<!--";
	include("proofgen.css");
	print "-->\n</style>\n";
        /* End style sheet paste in */
        print $line;
	$i++;
	break;
     } else { print $line; };
  }
  /* Now parse rest of document, hacking relative links. */
  /* Matching here is not great, will get confused by html tags inside strings, etc. */
  for (;$i < count($file);$i++)  {
     $line = $file[$i];
       /* PHP has no way to get the match position, so we have to 
	  match a suffix of the line, add extra parenthesis, and calculate it. */
     while (eregi("(<A([^>]*)(HREF=\"([^\"]+)\")(.*))",$line,$linebits)) { 
       /* found URL in a particularly simple form */
       $matchpos = strlen($line) - strlen($linebits[1]);
       print substr($line,0,$matchpos);		/* start of line */
       $line = $linebits[5];			/* rest of line after link */
       $urlbits = parse_url($linebits[4]);
       if ($urlbits["host"]=="") { 
	  /* Assume a relative link, let's hack it. */
	  /* Use same title */
	  $newurl = "htmlshow.php?title=" . urlencode($title);
	  if ($urlbits["path"]=="") {
	     /* A fragment in same file */
	     $newurl = $newurl . "&file=" 
	       . urlencode($filename) . "#" . $urlbits["fragment"];
	  } else {
	     /* Another file */
	     $newurl = $newurl . "&file=" 
	    	. urlencode(dirname($filename) . "/" . $urlbits["path"])
		. ($urlbits["fragment"]=="" ? "" : "#" . $urlbits["fragment"]);
	  };
	  print "<A " . $linebits[2] . " HREF=\"" . $newurl . "\"";
	} else { print "<A " . $linebits[2] . $linebits[3]; }
     };
     /* Hack on a header and footer */
     if (eregi("<BODY.*>",$line)) { 
       /* Assume there's nothing else interesting on the line, whoops. */
       print $line;
       small_header_body($title);
     } elseif (eregi("</BODY>",$line)) {
       /* Assume there's nothing else interesting on the line, whoops. */
       click_to_go_back();
       print $line;
     } else {
       print $line;
     };
  }
}



/* Display a small page with standard header, footer added on.
   Much like htmlshow.  */

function smallpage($filename,$text="",$title="",$message="") {
 if ( $text == "") { $text=$filename; };
 if ( $message == "") { $message=$title; };
 if ( $message == "") { $message=$filename; };
 $urlbits = parse_url($filename);
 hlink("smallpage.php"
       . "?title=" . urlencode($title) 
       . "&file=" . urlencode($urlbits["path"])
       . ($urlbits["fragment"]=="" ? "" : "#" . $urlbits["fragment"]),
	$text, $message);
}

/* Specialised version for projects */

function pgproject($filename,$title) {
   smallpage("projects/$filename.html",$title,"Proof General Project",$title);
}


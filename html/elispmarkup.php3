<?php
//
// Markup Emacs Lisp and Outline files
//
// David Aspinall, March 2000
//
// $Id$
//
//

function isexpanded($headingno,$expanded) {
  //  print "testing $headingno";
  $all = ereg("all",$expanded);
  $thisone = ereg("," . $headingno,$expanded);
  return ($all ? ! $thisone : $thisone);
}

function addexpanded($headingno,$expanded) {
  $all = ereg("all",$expanded);
  return ($all ? str_replace("," . $headingno,"",$expanded) :
	         $expanded . "," . $headingno);
}

function removeexpanded($headingno,$expanded) {
  $all = ereg("all",$expanded);
  return ($all ? $expanded . "," . $headingno : 
		 str_replace("," . $headingno,"",$expanded));
}

function link_toggle($headingno,$text,$thispage,$filename,$expanded) {
    if (isexpanded($headingno,$expanded)) {
      $newexpanded=removeexpanded($headingno,$expanded);
    } else {
      $newexpanded=addexpanded($headingno,$expanded);
    }
  print "<a name=\"$headingno\"><a href=\"$thispage";
  print "?file=" . urlencode($filename);
  print "&expanded=" . urlencode($newexpanded) . "#" . $headingno . "\">" . $text . "</a></a>\n";
}

// FIXME: this is a nonsense really.  Might be okay if it
// used dynamic HTML but it's too much of a faff at the moment.
// Also, we should use the tree structure properly and keep a stack!

function outline_markup($filename,$thispage,$expanded)  {
  if ($title=="") { $title=$filename; };
  $outline = false;
  $file = file($filename);
  $i = 0;
  $level=0;
  $headingno=0;
  /* Now parse file, watching for outline headers */
  for (;$i < count($file);$i++)  {
     $line = $file[$i];
     // HTML escapes
     $line = htmlentities($line);
     // Anchors for URLs
     $line = ereg_replace("((http://|mailto:)[-a-zA-Z0-9\.~/_@]+)","<a href=\"\\1\">\\1</a>",$line);
     // Assume a heading
     $multipar=false;
     if (ereg("-\*- (mode:)?outline -\*-",$line)) {
       // Found line with outline mode header, set flag
       // and print message
       $outline = true;
       print "<p><i>";
       print "This is a flattened outline file: click on a title to hide/reveal the leaf underneath it.";
       print "<br>Click "; 
       print "<a href=\"$thispage?file=" . urlencode($filename);
       print "&expanded=all\">here</a> to show whole body, or ";
       print "<a href=\"$thispage?file=" . urlencode($filename);
       print "\">here</a> to hide whole body.";
       print "</i></p>\n";
     } elseif ($outline) {
       if (ereg("^ *\n",$line)) {
	 // if (!newpara) { print "</p><p>\n"; };
	 $newpara = true;
       } elseif (ereg("^([\*]+) (.*)\n",$line,$heading)) {
	 $newlevel = strlen($heading[1])+1;
	 //	 if ($newlevel < $level) {
	 // Up a level
	 //  $p = strpos($path,"-");
	 //  $path = substr($path,0,$p-1);
	 if ($newpara && 
	     $level<=$newlevel && 
	     isexpanded($headingno,$expanded)) { print "<p>\n"; }
	 $headingno++;
	 $level=$newlevel;
	 $text="<h$level>$heading[2]</h$level>";
	 link_toggle($headingno,$text,$thispage,$filename,$expanded);
       } elseif (isexpanded($headingno,$expanded)) {
	 if ($newpara && $level==0) { print "<p>\n"; }
	 print $line;
	 $newpara=false;
	 $level=0;
       }
     } else {
       print $line;
     }
  }
}

//
// For browsing source.  Unfinished.
//

function elisp_markup($filename,$thispage,$title="")  {
  if ($title=="") { $title=$filename; };
  $file = file($filename);
  $i = 0;
  $level=0;
  $headingno=0;
  /* Now parse file, watching for outline headers */
  for (;$i < count($file);$i++)  {
     $line = $file[$i];
     // HTML escapes
     $line = htmlentities($line);
     // Anchors for URLs
     $line = ereg_replace("((http://|mailto:)[-a-zA-Z0-9\.~/_@]+)","<a href=\"\\1\">\\1</a>",$line);
     // Font-lock equivalents...
     // 1. comments.  Strings roughly done: ignore if quote appears after ;
// seems buggy.
//     $line = ereg_replace("^([^;]*)(\;+[^\"]+)$",
//		          "\\1<div style=\"color: #8080E0\">\\2</div>",
//			  $line);
     // 2. keywords
     // FIXME: this inserts CR's.
//     $line = ereg_replace("^\(def(macro|un|var|custom|const|group)",
//			  "(<div style=\"color: #C0B0B0\">def\\1</div>",
//			  $line);
     // FIXME: add hrefs for keywords, looking up in TAGS file.
     // FIXME: add line numbers
     // FIXME: parse strings
     print $line;
  }
}

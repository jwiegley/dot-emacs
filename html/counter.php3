<?php
/*
 * Increment an access counter.
 * David Aspinall, June 1999.
 *
 * $Id$
 *
 */

$counterFile = "counter.txt";
$counterStart = "counterstart.txt";
$maxlen = 10;

// NB: probably have trouble with permissions 
//     if file doesn't exist already, so start with
//     empty files made with touch.

// Here's how to cause it to be initialized:
//
//  rm -f counter.txt counterstart.txt
//  touch counter.txt counterstart.txt
//  chmod o+w counter.txt counterstart.txt
//

if (is_readable($counterFile) && is_writeable($counterFile)) {
  $fp   = fopen($counterFile,"r+");
  if (filesize($counterFile)<1) {
     // Start counter, write a timestamp.
     $num = 1;
     if (is_readable($counterStart) && is_writeable($counterStart)) {
	$fps = fopen($counterStart,"w");
        fputs($fps,time());
        fclose($fps);
        print "<!-- Hit counter initialized. -->";
     } else {
        print "<!-- Hit counter initialized, but timestamp could not be set -->";
     };
  } else {
     $num  = fgets($fp,$maxlen);
     $num += 1;
     print "<!-- Hit counter: $num -->";
  };
  rewind($fp);
  fputs($fp,$num);
  fclose($fp);
} else {
  print "<!-- Hit counter file $counterFile cannot be accessed. -->";
};
?>


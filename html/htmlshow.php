<?php
  require('functions.php3');
  if (substr($file,0,1)=="." or 
      substr($file,0,1)=="/" or
      substr($file,0,1)=="~") {
     print "Sorry, can't show you that file!\n"; 
  } else {
     hack_html($file,$title);
  }
  footer(); 
?>

<?php
  require('functions.php3');
  small_header($title);
  if (substr($file,0,1)=="." or 
      substr($file,0,1)=="/" or
      substr($file,0,1)=="~") {
     print "Sorry, can't show you that file!\n"; 
  } else {
    include($file);
  }
  footer(); 
?>

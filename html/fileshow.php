<?php
  require('functions.php3');
  require('elispmarkup.php3');
  $filename=$HTTP_GET_VARS["file"];
  $title=$HTTP_GET_VARS["title"];
  $expanded=$HTTP_GET_VARS["expanded"];
  fileshowmarkup($file,$title,$expanded);
?>

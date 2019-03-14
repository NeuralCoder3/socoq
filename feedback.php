<?php

error_reporting(E_ALL);

if (isset($_GET["error"])) {
    echo "An error occured.";
    exit();
}

if(!isset($_POST["message"])) {
    ?>
<form method="post" action="./feedback.php">
    <p><label>Message:<br>
    <textarea name="message" cols="50" rows="8"></textarea></label></p>
    <input type="submit" value="Send">
</form>
    <?php
    exit();
}

// $mailTo = 'ullrich.marcel@web.de';
// $mailFrom = '"CoqIDE" <coqide@coq.bplaced.net>';
// $mailSubject    = 'Feedback';
//  $returnPage = 'index.php';
//  $returnErrorPage = 'feedback.php?error=true';
$mailText = "";

if(isset($_POST)) {
   foreach($_POST as $name => $value) {
      if(is_array($value)) {
          $mailText .= $name . ":\n";
          foreach($valueArray as $entry) {
             $mailText .= "   " . $value . "\n";
          }
      }
      else {
          $mailText .= $name . ": " . $value . "\n";
      }
   }
}

 if(get_magic_quotes_gpc()) {
     $mailText = stripslashes($mailText);
 }

 file_put_contents("./feedback/".uniqid().".txt",$mailText);

echo "Feedback saved.<br><a href=\"index.php\" title=\"To the editor\">Back</a>";

//
// $mailSent = @mail($mailTo, $mailSubject, $mailText, "From: ".$mailFrom);
//
// if($mailSent == TRUE) {
//    header("Location: " . $returnPage);
// }
// else {
//     echo "Error<br>";
//     print_r(error_get_last());
//    // header("Location: " . $returnErrorPage);
// }
//
// exit();

?>

<?php
require("ids.php");

$file = $_POST["file"];
$file = sanitizeFile($file);
$file = "./data/public/".$file.".v";
$a=file_get_contents($file);
if ($a) {
    echo $a;
} else {
    echo "Error while loading.";
}
?>

<?php
require("ids.php");

$username = $_POST["username"];
if($username!="")
    $computerId=sanitizeFile($username);

$files = glob('./data/'.$computerId.'_*.v');
$first=true;
foreach ($files as $f) {
    if ($first) {
        $first=false;
    }else{
        echo "<br>";
    }
    $f=str_replace($computerId."_", "", basename($f, ".v"));
    // if ($f=="") {
    //     $f="&nbsp;";
    // }
    echo "<button>".$f."</button>";
}
?>

<?php
require("ids.php");

$file = $_POST["file"];
$file = sanitizeFile($file);
$data = $_POST["data"];
$save = $_POST["save"]=="true";
$username = $_POST["username"];
$official = $_POST["official"]=="true";
$filename="";
if($username!="")
    $computerId=sanitizeFile($username);
if ($official) {
    if($save){
        $filename=uniqid();
    } else {
        $filename=$file;
    }
    $file = "./data/official/".$filename.".v";
} else {
    $filename=$computerId."_".$file;
    $file = "./data/".$filename.".v";
}
if ($save) {
    file_put_contents($file, $data);
    if ($official) {
        // echo "http://".$_SERVER["HTTP_HOST"].$_SERVER["REQUEST_URI"]."?=".$filename;//substr($file,2);
        echo "http://".$_SERVER["HTTP_HOST"].str_replace("save","index",$_SERVER["REQUEST_URI"])."?url=".$filename;//substr($file,2);
    }else{
        echo "1";
    }
} else {
    $a=file_get_contents($file);
    if ($a) {
        echo $a;
    } else {
        echo "Error while loading file.";//": ".$file." ".$computerId.".";
    }
}
?>

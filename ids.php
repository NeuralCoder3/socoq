<?php
error_reporting(0);

$computerId = md5($_SERVER['HTTP_USER_AGENT'].gethostname());//.$_SERVER['REMOTE_ADDR']);

function sanitizeFile($file){
    $file = mb_ereg_replace("([^\w\s\d\-_~,;\[\]\(\).])", '', $file);
    $file = mb_ereg_replace("([\.]{2,})", '', $file);
    return $file;
}

?>

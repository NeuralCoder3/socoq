<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <meta http-equiv="content-type" content="text/html;charset=utf-8" />
    <link rel="stylesheet" href="main.css" />
    <script src="./jquery-3.3.1.min.js"></script>
    <title>SOCOQ</title>
    <link rel="stylesheet" href="main2.css" />
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.7.0/css/font-awesome.min.css" />
    <meta property="og:image" content="http://coq.bplaced.net/oct.png">
    <meta property="og:image:type" content="image/png">
    <meta property="og:image:width" content="1024">
    <meta property="og:image:height" content="1024">
    <meta property="og:type" content="website" />
    <meta property="og:url" content="http://coq.bplaced.net/"/>
    <meta property="og:title" content="SOCOQ" />
    <meta property="og:description" content="Online Proofing with Coq." />
  </head>
  <body>
      <?php
$isFirefox=false;
if(strpos( $_SERVER['HTTP_USER_AGENT'],"Firefox/")){
    ?>
    <style>
        dialog{
            margin-top: 10%;
        }
    </style>
    <?php
    $isFirefox=true;
}
       ?>
  <dialog id="publicdialog">
<?php if(!$isFirefox){ ?><form method="dialog"><?php } ?>
      <div id="documents">
        <?php
$files = glob('./data/public/*.v');
$first=true;
foreach ($files as $f) {
    if ($first) {
        $first=false;
    }else{
        echo "<br>";
    }
    echo "<button>".basename($f,".v")."</button>";
}
?>
      </div>
      <menu>
        <button value="cancel" onclick="closeDialog('publicdialog');">Cancel
        </button>
      </menu>
<?php if(!$isFirefox){ ?></form><?php } ?>
  </dialog>
  <dialog id="owndialog">
<?php if(!$isFirefox){ ?><form method="dialog"><?php } ?>
      <div id="ownfiles">
      </div>
      <menu>
        <button value="cancel" onclick="closeDialog('owndialog');">Cancel
        </button>
      </menu>
<?php if(!$isFirefox){ ?></form><?php } ?>
  </dialog>
  <dialog id="settingsdialog">
<?php if(!$isFirefox){ ?><form method="dialog"><?php } ?>
      <div id="settings">
        <table>
          <tr>
            <td>Theme:</td>
            <td>
              <select id="themeselection">
                <option value="ambiance">ambiance</option>
                <option value="default">default</option>
                <option value="abcdef">abcdef</option>
                <option value="blackboard">blackboard</option>
                <option value="hopscotch">hopscotch</option>
                <option value="solarized">solarized</option>
                <option value="dracula">dracula</option>
                <option value="monokai">monokai</option>
                <!-- <option value="paraiso-light">paraiso-light</option> -->
              </select>
            </td>
          </tr>
          <tr>
            <td>Vim-Mode:</td>
            <td>
              <input type="checkbox" id="vim-mode">
            </td>
          </tr>
          <tr>
            <td>Username:</td>
            <td>
              <input type="text" id="username" placeholder="Username" value="">
            </td>
          </tr>
          <tr>
            <td>Autocomplete (Ctrl+Space)</td>
            <td>
              <input type="checkbox" id="autocomplete"> (don't fool yourself!)
            </td>
          </tr>
          <tr>
            <td>Snippets (Ctrl+S)</td>
            <td>
              <input type="checkbox" id="snippet"> (don't fool yourself!)
            </td>
          </tr>
        </table>
      </div>
      <menu>
        <button value="close" onclick="closeDialog('settingsdialog');">Close
        </button>
      </menu>
<?php if(!$isFirefox){ ?></form><?php } ?>
  </dialog>
    <div id="ide-wrapper" class="toggled">
      <div id="code-wrapper">
        <div id="document">
          <div class="spoiler-forum spoiler-hidden">
            <a class="spoiler-toggle" href="#">
              <strong id="verstecken">Hinweise
              </strong>
            </a>
            <div class="spoiler-text" id="versteckt">
<pre>  Please wait until loading finished.
  Go back one statement [Alt]+[Up].
  Execute next statement [Alt]+[Down].
  Execute to cursor [Alt]+[Enter].
  Toggle the right panel with [F8].
  Status Informations are shown on the right panel
   and in the status bar below.
  When Importing Librarys it is necessary
   to write "From Coq Require Import".<?php
   if($isFirefox) echo "\n  Please activate dom.dialog_element\n   in about:config."; ?>
</pre>
            </div>
          </div>
          <br>
          <script type="text/javascript">
            $('#verstecken').click(function() {
              if ($('#versteckt').is(":hidden"))
              {
                $('#versteckt').slideDown("slow");
              }
              else {
                $('#versteckt').slideUp("slow");
              }
              return false;
            });
          </script>
          <div class="rcorners2 headpanel">
            <input type="input" id="file" size="10" placeholder="Filename">
            <button onclick="save();">
              <i class="fa fa-floppy-o">
              </i>Save
            </button>
            <button onclick="load();">
              <i class="fa fa-file-o">
              </i>Load
            </button>
            <button onclick="share();">
              <i class="fa fa-link">
              </i>Share
            </button>
            <button onclick="public();">
              <i class="fa fa-list-alt">
              </i>Public
            </button>
            <button onclick="settings();">
              <i class="fa fa-cogs">
              </i>
            </button>
          </div>
          <div>
            <textarea id='coq-ide'>
<?php
if(isset($_GET["url"])){
    $_POST["file"]=$_GET["url"];
    $_POST["data"]="";
    $_POST["save"]="false";
    $_POST["official"]="true";
    require("save.php");
} else {
?>From Coq Require Import Arith List Omega Bool Program.Tactics.

Goal forall (n:nat), True.
Proof.
  intros x.
  exact I.
Qed.<?php
}
?></textarea>
                <script type="text/javascript">
var loadedURL=<?php if(isset($_GET["url"])){echo "true";}else{echo "false";} ?>;
var myNewURL = refineURL();
window.history.pushState("object or string", "Title", "/" + myNewURL );
function nthIndex(str, pat, n){
    var L= str.length, i= -1;
    while(n-- && i++<L){
        i= str.indexOf(pat, i);
        if (i < 0) break;
    }
    return i;
}
function refineURL()
{
    var currURL= window.location.href;
    var afterDomain= currURL.substring(nthIndex(currURL,'/',3) + 1);
    var beforeQueryString= afterDomain.split("?")[0];
    return beforeQueryString;
}
                </script>
          </div>
        </div>
      </div>
    </div>
    <script type="text/javascript">
    var coqdoc_ids = ['coq-ide'];
    </script>
    <script src="./ui-js/jscoq-loader.js" type="text/javascript">
    </script>
    <script type="text/javascript">
      $("#autocomplete").change(function(){
        localStorage.setItem('coq-useAutocomplete', $(this).prop("checked"));
        useAutoComplete=$(this).prop("checked");
      });
      $("#vim-mode").change(function(){
        localStorage.setItem('coq-vim-mode', $(this).prop("checked"));
        editor.setOption("vimMode", $(this).prop("checked"));
      });
        $("#snippet").change(function(){
          localStorage.setItem('coq-useSnippet', $(this).prop("checked"));
          useSnippets=$(this).prop("checked");
        });
      $("#themeselection").change(function(){
        localStorage.setItem('coq-theme', $(this).val());
        editor.setOption("theme", $(this).val());
      });
      $("#username").change(function(){
        username=$(this).val();
        localStorage.setItem('coq-username', username);
      });
      $("#documents").find( "button" ).each(function (index) {
        $(this).click(function(){
          $.post('load.php',
            { file: $(this).text() },
            function( data ){
              editor.setValue(data);
              $("#info").html(" - File loaded.");
            }
          );
        });
      });
      function save() {
        $.post('save.php',
          {
            data: editor.getValue(),
            save: "true",
            file: $("#file").val(),
            official: "false",
            username: username
          },
          function( data ){
            $("#info").html(" - Saved file.");
          }
        );
      }
      function load() {
        document.getElementById("owndialog").showModal();
        $.post('list.php',
          { username: username },
          function( data ){
            $("#ownfiles").html(data);
            $("#ownfiles").find( "button" ).each(function (index) {
              $(this).click(function(){
                var filename=$(this).text();
                $.post('save.php',
                  {
                    data: "",
                    save: "false",
                    file: filename,
                    official: "false",
                    username: username
                  },
                  function( data ){
                    editor.setValue(data);
                    $("#info").html(" - File loaded.");
                  }
                );
              });
            });
          }
        );
      }
      function share() {
        $.post('save.php',
          {
            data: editor.getValue(),
            save: "true",
            file: "",
            official: "true"
          },
          function( data ){
            $("#info").html(" - Saved under <a href=\""+data+"\">"+data+"</a>");
          }
        );
      }
      function public() {
        document.getElementById("publicdialog").showModal();
      }
      function settings() {
        document.getElementById("settingsdialog").showModal();
      }
      function closeDialog(id) {
          // console.log("Close ID: "+id);
        document.getElementById(id).close();
      }
    </script>
    <script type="text/javascript">
      var coq;
      var editor;
      loadJsCoq('./')
        .then(loadJs("./ui-external/CodeMirror/addon/runmode/runmode"))
        .then(loadJs("./ui-external/CodeMirror/addon/runmode/colorize"))
        .then( function () {
        var coqInline = document.getElementsByClassName("inline-coq");
        CodeMirror.colorize(coqInline);
      }).then( function () {
        coq = new CoqManager (coqdoc_ids,
                              {
                                  base_path: './',
                                  init_pkgs: ['init', 'coq-reals']
                              }
                             );
        $(".exits").hide();
        $("#hide-panel").hide();
        $("#goal-text").css("background-color","transparent");
        $("#goal-text").bind("DOMSubtreeModified",function(){
          var text=$("#goal-text").html();
          if(!text.includes("JsCoq"))
            return
            var newtext="Coq 8.7.0\nOCaml 4.06.0\nJSOCaml 3.0.1";
          if(text.includes("filesystem"))
            newtext+="\n\nFilesystem loaded";
          if(text.includes("packages"))
            newtext+="\nPackages loaded";
          $("#goal-text").html(newtext);
          window.dispatchEvent(new Event('resize'));
        });
        var bgColor="#D0FFCF";
        var bgColor2="#DCFFFF";
        $("#buttons").css("background-color",bgColor);
        $("#buttons").addClass("rcorners1");
        $("body").css("background-color",bgColor2);
        $("#toolbar").css("border-bottom","0px");
        $("#code-wrapper").css("background-color","transparent");
        $("#document").css("background-color","transparent");
        $("#panel-wrapper").css("background-color","transparent");
        $(".flex-container").addClass("rcorners1");
        $(".flex-container").css("background-color",bgColor);
        $(".flex-container").css("padding-bottom","50px");//25px
        $(".flex-container").css("border","1px solid black");
        $("#buttons").css("border","1px solid black");
        $("#buttons").css("height","60px");
        $("#buttons").css("padding","12px");
        $("[name='up']").removeAttr("width");
        $("[name='down']").removeAttr("width");
        $("[name='to-cursor']").removeAttr("width");
        $("[name='up']").attr("height","30");
        $("[name='down']").attr("height","30");
        $("[name='to-cursor']").attr("height","30");
        $("[name='msg_filter']").hide();
        $(".flex-panel").each(function (index) {
          $(this).css("background-color",bgColor);
          $(this).css("border","0px solid black");
          $(this).addClass("rcorners2");
          $(this).css("overflow-x","hidden");
        });
        $(".caption").each(function (index) {
          $(this).addClass("rcorners2");
          $(this).css("border-top","1px solid black");
        });
        editor = $('.CodeMirror')[0].CodeMirror;

        var val=localStorage.getItem('coq-snippet');
        if(val !== null && !loadedURL)
          editor.setValue(val);
        var theme=localStorage.getItem('coq-theme');
        console.log("Theme: "+theme);
        if(theme === null)
          theme="ambiance";
        $("#themeselection").val(theme);
        editor.setOption("theme", theme);
        username=localStorage.getItem('coq-username');
        if(username === null)
          username="";
        $("#username").val(username);
        filename=localStorage.getItem('coq-filename');
        if(filename === null)
          filename="";
        $("#file").val(filename);

        useAutoComplete=localStorage.getItem('coq-useAutocomplete')=="true";
        var vimMode=localStorage.getItem('coq-vim-mode')=="true";
        editor.setOption("vimMode", vimMode);
        useSnippets=localStorage.getItem('coq-useSnippet')=="true";

        $("#snippet").prop("checked", useSnippets);
        $("#autocomplete").prop("checked", useAutoComplete);
        $("#vim-mode").prop("checked", vimMode);

      });
      function save_coq_snippets(){
        localStorage.setItem('coq-snippet', editor.getValue());
        localStorage.setItem('coq-filename', $("#file").val());
      }
      window.onbeforeunload = save_coq_snippets;
    </script>
    <footer>
      <a href="feedback.php" title="anonymous feedback">Marcel Ullrich</a> - Based on
      <a href="https://github.com/ejgallego/jscoq">JsCoq</a>
      <span id="info">
      </span>
       - <a href="https://github.com/NeuralCoder3/socoq">Source Code</a>
    </footer>
  </body>
</html>

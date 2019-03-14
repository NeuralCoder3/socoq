"use strict";

class CmSentence {

    constructor(start, end, text, is_comment) {
        // start, end: {line: l, ch: c}
        this.start = start;
        this.end   = end;
        this.text  = text;
        this.mark  = undefined;
        this.is_comment = is_comment;
    }

}

var edit;
var useSnippets=false;
var useAutoComplete=false;

class CmCoqProvider {

    constructor(element) {

            var words = [
              'Abort', 'About', 'Add', 'All', 'Arguments', 'Asymmetric', 'Axiom',
              'Bind',
              'Canonical', 'Check', 'Class', 'Close', 'Coercion', 'CoFixpoint', 'Comments',
              'CoInductive', 'Context', 'Constructors', 'Contextual', 'Corollary',
              'Defined', 'Definition', 'Delimit',
              'Fail',
              'Eval',
              'End', 'Example', 'Export',
              'Fact', 'Fixpoint', 'From',
              'Global', 'Goal', 'Graph',
              'Hint', 'Hypotheses', 'Hypothesis',
              'Implicit', 'Implicits', 'Import', 'Inductive', 'Infix', 'Instance',
              'Lemma', 'Let', 'Local', 'Ltac',
              'Module', 'Morphism',
              'Next', 'Notation',
              'Obligation', 'Open',
              'Parameter', 'Parameters', 'Prenex', 'Print', 'Printing', 'Program',
              'Patterns', 'Projections', 'Proof',
              'Proposition',
              'Qed',
              'Record', 'Relation', 'Remark', 'Require', 'Reserved', 'Resolve', 'Rewrite',
              'Save', 'Scope', 'Search', 'SearchAbout', 'Section', 'Set', 'Show', 'Strict', 'Structure',
              'Tactic', 'Time', 'Theorem', 'Types',
              'Unset',
              'Variable', 'Variables', 'View'
            ,
              'as',
              'at',
              'cofix', 'crush',
              'else', 'end',
              'False', 'fix', 'for', 'forall', 'fun',
              'if', 'in', 'is',
              'let',
              'match',
              'of',
              'Prop',
              'return',
              'struct',
              'then', 'True', 'Type',
              'when', 'with'
            ,
              'after', 'apply', 'assert', 'auto', 'autorewrite',
              'case', 'change', 'clear', 'compute', 'congruence', 'constructor',
              'congr', 'cut', 'cutrewrite',
              'dependent', 'destruct',
              'eapply', 'eassumption', 'eauto', 'econstructor', 'elim', 'exists',
              'field', 'firstorder', 'fold', 'fourier',
              'generalize',
              'have', 'hnf',
              'induction', 'injection', 'instantiate', 'intro', 'intros', 'inversion',
              'left',
              'move',
              'pattern', 'pose',
              'refine', 'remember', 'rename', 'replace', 'revert', 'rewrite',
              'right', 'ring',
              'set', 'simpl', 'specialize', 'split', 'subst', 'suff', 'symmetry',
              'transitivity', 'trivial',
              'unfold', 'unlock', 'using',
              'vm_compute',
              'where', 'wlog'
            ,
              'assumption',
              'by',
              'contradiction',
              'discriminate',
              'exact',
              'now',
              'omega',
              'reflexivity',
              'tauto'
            ,
              'admit',
              'Admitted'
            ];


  function hints(cm, option) {
    return new Promise(function(accept) {
      setTimeout(function() {
          if (!useAutoComplete) {
              return accept(null);
          }
        var cursor = cm.getCursor(), line = cm.getLine(cursor.line)
        var start = cursor.ch, end = cursor.ch
        while (start && /\w/.test(line.charAt(start - 1))) --start
        while (end < line.length && /\w/.test(line.charAt(end))) ++end
        var word = line.slice(start, end);
        var wordlist=[];
        for (var i = 0; i < words.length; i++) {
            if (words[i].startsWith(word)) {
                wordlist.push(words[i]);
            }
        }
        if (wordlist.length>0) {
            return accept({list: wordlist,
                           from: CodeMirror.Pos(cursor.line, start),
                           to: CodeMirror.Pos(cursor.line, end)})
        }else{
            return accept(null);
        }
      }, 100)
    })
  }


  var snippets = [
    { text: 'Goal True.\nProof.\nQed.', displayText: 'Proof' },
    { text: 'match n with\n  | O => True\n  | S _ => False\nend.', displayText: 'match' },
    { text: 'Fixpoint even n : Prop :=\nmatch n with\n  | O => True\n  | S O => False\n  | S (S m) => even m\nend.', displayText: 'Fixpoint' },
    { text: 'Inductive NAME : Type :=\n| CONST1 : NAME\n| CONST2 : forall (n:nat), NAME.', displayText: 'Inductive' },
];

  function snippet() {
      if (!useSnippets) {
          return;
      }
    CodeMirror.showHint(edit, function () {
      const cursor = edit.getCursor()
      const token = edit.getTokenAt(cursor)
      const start = token.start
      const end = cursor.ch
      const line = cursor.line
      const currentWord = token.string

      const list = snippets.filter(function (item) {
        return item.text.indexOf(currentWord) >= 0
      })

      return {
        list: list.length ? list : snippets,
        from: CodeMirror.Pos(line, start),
        to: CodeMirror.Pos(line, end)
      }
    }, { completeSingle: false })
  }

        var cmOpts =
            {
                mode : "coq",
                // mode : { name : "coq",
                //        version: 4,
                //        singleLineStringErrors : false
                //      },
              lineNumbers   : true,
              indentUnit    : 2,
              matchBrackets : true,
              extraKeys: {
                        "Ctrl-Space": "autocomplete",
                        "Ctrl-S": function() {snippet()},
                        "Ctrl-Q": function(cm){ cm.foldCode(cm.getCursor()); }
                      },
    foldGutter: true,
    gutters: ["CodeMirror-linenumbers", "CodeMirror-foldgutter"],
              hintOptions: {hint: hints},
               theme         : 'ambiance',
               keyMap        : "sublime"
            };

        if (typeof element === 'string' || element instanceof String) {
            this.editor = CodeMirror.fromTextArea(document.getElementById(element), cmOpts);
        } else {
            this.editor = CodeMirror(element, cmOpts);
        }

        edit=this.editor;

        this.editor.on('change', evt => this.onCMChange(evt) );
        // From XQuery-CM
        CodeMirror.on(this.editor.getWrapperElement(), "mouseenter",
                      evt => this.onCMMouseEnter(this.editor, evt));
        CodeMirror.on(this.editor.getWrapperElement(), "mouseleave",
                      evt => this.onCMMouseLeave(this.editor, evt));
    }

    focus() {
        this.editor.focus();
    }

    // If prev == null then get the first.
    getNext(prev) {

        var start = {line : 0, ch : 0};
        var doc = this.editor.getDoc();

        if (prev) {
            start = prev.end;
        }

        // EOF
        if (start.line === doc.lastLine() &&
            start.ch === doc.getLine(doc.lastLine()).length) {
            return null;
        }

        var token = this.getNextToken(start, /statementend|bullet|brace/);
        if (!token) return null;

        var end = {line : token.line, ch : token.end};

        for (var mark of doc.findMarks(end,end)) {
            mark.clear();
        }

        var stm = new CmSentence(start, end,
                                 doc.getRange({line : start.line, ch : start.ch},
                                              {line : token.line, ch : token.end}),
                                 token.type === 'comment'
                                );
        return stm;
    }

    // Gets sentence at point;
    getAtPoint() {

        var doc   = this.editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        // XXX
        if (marks.length) {
            return marks[0].stm;
        } else {
            return null
        }
        // } while(stm && (stm.end.line < cursor.line || stm.end.ch < cursor.ch));
    }

    // Mark a sentence with {clear, processing, error, ok}
    mark(stm, mark) {

        var doc = this.editor.getDoc();

        switch (mark) {
        case "clear":
            stm.mark.clear();
            stm.mark = null;
            // XXX: Check this is the right place.
            // doc.setCursor(stm.start);
            break;
        case "processing":
            stm.mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-pending'});
            stm.mark.stm = stm;
            break;
        case "error":
            stm.mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-failed'});
            stm.mark.stm = stm;
            // XXX: Check this is the right place.
            doc.setCursor(stm.end);
            break;
        case "ok":
            stm.mark = doc.markText(stm.start, stm.end, {className : 'coq-eval-ok'});
            stm.mark.stm = stm;
            // XXX: Check this is the right place.
            // This interferes with the go to target.
            // doc.setCursor(stm.end);
            break;
        }
    }

    cursorLess(c1, c2) {

        return (c1.line < c2.line ||
                (c1.line === c2.line && c1.ch <= c2.ch));
    }

    cursorToStart(stm) {

        var doc = this.editor.getDoc();
        var csr = doc.getCursor();

        if (this.cursorLess(csr, stm.end))
            doc.setCursor(stm.start);
    }

    cursorToEnd(stm) {
        var doc = this.editor.getDoc();
        var csr = doc.getCursor();

        if (this.cursorLess(csr, stm.end))
            doc.setCursor(stm.end);
    }

    // If any marks, then call the invalidate callback!
    onCMChange(evt) {

        var doc   = this.editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        // We assume that the cursor is positioned in the change.
        if (marks.length === 1) {
            // XXX: Notify of the latest mark.
            this.onInvalidate(marks[0].stm);
        } else if (marks.length > 1) {
            console.log("Cursor in mark boundary, invalidating the first...");
            this.onInvalidate(marks[0].stm);
        }
    }

    // If a mark is present, request contextual information.
    onCMMouseEnter(editor,evt) {

        var doc   = editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        // We assume that the cursor is positioned in the change.
        if (marks.length === 1) {
            // XXX: Notify of the latest mark.
            this.onMouseEnter(marks[0].stm);
        } else if (marks.length > 1) {
            console.log("Trying the first mark of", marks.length);
            this.onMouseEnter(marks[0].stm);
        }
    }

    // Notification of leaving the mark.
    onCMMouseLeave(editor,evt) {

        var doc   = editor.getDoc();
        var marks = doc.findMarksAt(doc.getCursor());

        // We assume that the cursor is positioned in the change.
        if (marks.length === 1) {
            // XXX: Notify of the latest mark.
            this.onMouseLeave(marks[0].stm);
        } else if (marks.length > 1) {
            console.log("Trying the first mark of", marks.length);
            this.onMouseLeave(marks[0].stm);
        }
    }


    // CM specific functions.

    // Returns the next token after the one seen at position: {line:…, ch:…}
    // type_re: regexp to match token type.
    // The returned object is a CodeMirror token with an additional attribute 'line'.
    getNextToken(position, type_re) {
        var cm = this.editor;
        var linecount = cm.getDoc().lineCount();
        var token, next, ch, line;
        do {
            token = cm.getTokenAt(position);
            ch = token.end + 1;
            line = position.line;
            if (token.end === cm.getLine(line).length) {
                line++;
                ch = 0;
                if (line >= linecount)
                    return null;
            }
            next = cm.getTokenAt({line:line, ch:ch});
            next.line = line;
            position = {line:next.line, ch:next.end};
        } while(type_re && !(type_re.test(next.type)));
        return next;
    }

}

// Local Variables:
// js-indent-level: 4
// End:

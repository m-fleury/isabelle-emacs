;;; lsp-isar-indent.el --- Indentation of isar files -*- lexical-binding: t; -*-

;; Author: Mathias Fleury <mathias.fleury@protonmail.com>
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/

;; Keywords: lisp
;; Version: 0
;; Package-Requires: ((emacs "25.1"))

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and-or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

;;; Commentary:

;; blabal

;;; Code:

(require 'thingatpt)

(defun lsp-isar-indent-current-line-empty-p ()
  (or (not (thing-at-point 'line)) (string-match-p "^\\s-*$" (thing-at-point 'line))))

(defun lsp-isar-indent-create-regex-from-words (s)
  "Creates a regular expression based on a list of words."
  (concat
   (cl-reduce (lambda (w y) (concat w "\\|" y))
	      (mapcar (lambda (w) (concat "\\(" w "\\)"))
		      s))))

(defvar lsp-isar-indent-keyw-quasi-command
  (list
   "and" "assumes" "constrains" "defines" "fixes" "for" "if" "includes" "notes" "rewrites"
   "obtains" "shows" "when" "where" "imports" "theory" "datatype")) ;; missing "|"

(defvar lsp-isar-indent--keyw-quasi-command
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-quasi-command))

(defvar lsp-isar-indent-keyw-command-open
  (list "begin" "proof"))

(defvar lsp-isar-indent--keyw-command-open
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-command-open))

(defvar lsp-isar-indent-keyw-command-close
  (list "qed" "end"))

(defvar lsp-isar-indent--keyw-command-close
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-command-close))

(defvar lsp-isar-indent-keyw-theory
  (list "theory" "imports" "end" "begin"))

(defvar lsp-isar-indent--keyw-theory
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-theory))

(defvar lsp-isar-indent-trace-indent t)


(defun lsp-isar-indent-trace-indent (&rest args)
  (if lsp-isar-indent-trace-indent
      (apply 'message args)))

(defvar lsp-isar-indent-keyw-diag
  (list
   "export_generated_files" "ML_val" "ML_command" "print_bundles" "help"
   "print_commands" "print_options" "print_context" "print_theory" "print_definitions"
   "print_syntax" "print_abbrevs" "print_defn_rules" "print_theorems" "print_locales"
   "print_classes" "print_locale" "print_interps" "print_dependencies" "print_attributes"
   "print_simpset" "print_rules" "print_trans_rules" "print_methods"
   "print_antiquotations" "print_ML_antiquotations" "thy_deps" "locale_deps" "class_deps"
   "thm_deps" "print_term_bindings" "print_facts" "print_cases" "print_statement" "thm" "prf"
   "full_prf" "prop" "term" "typ" "print_codesetup" "unused_thms" "print_state" "welcome"
   "find_theorems" "find_consts"))

(defvar lsp-isar-indent--keyw-diag
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-diag))

(defvar lsp-isar-indent-keyw-thy_decl
  (list
   "default_sorts" "typedecl" "type_synonym" "nonterminal" "judgement"
   "typedecl" "type_synonym" "nonterminal" "judgment"
   "consts" "syntax" "no_syntax" "translations" "no_translations"
   "definition" "abbreviation" "type_notation" "no_type_notation" "notation"
   "no_notation" "axiomatization" "alias" "type_alias" "lemmas" "declare"
   "hide_class" "hide_type" "hide_const" "hide_fact"))

(defvar lsp-isar-indent--keyw-thy_decl
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-thy_decl))

(defvar lsp-isar-indent-keyw-thy-goal
  (list "theorem" "lemma" "corollary" "proposition"))

(defvar lsp-isar-indent--keyw-thy-goal
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-thy-goal))

(defvar lsp-isar-indent-thy_decl_block
  (list "context" "locale" "experiment"
	"bundle" "instantiation" "overloading"
	"notepad"))

(defvar lsp-isar-indent--keyw-thy_decl
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-thy_decl))

(defcustom lsp-isar-base-offset 2
  "Amount of basic offset used by + and - symbols in `c-offsets-alist'."
  :type 'integer
  :group 'isabelle)


(defvar lsp-isar-indent-keyw-qed
  (list "by" "\\.\\." "\\." "sorry" "\\\\<proof>"))

(defvar lsp-isar-indent--keyw-qed
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-qed))

(defvar lsp-isar-indent-keyw-proof-enclose
  (list "qed" "done" "end" "next" "subgoal"))

(defvar lsp-isar-indent--keyw-proof-enclose
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-proof-enclose))

(defvar lsp-isar-indent-keyw-proof-enclose_not_done
  (list "qed" "end" "next"))

(defvar lsp-isar-indent--keyw-proof-enclose_not_done
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-proof-enclose_not_done))

(defvar lsp-isar-indent-keyw-open-bracket
  (list "{"))

(defvar lsp-isar-indent--keyw-open-bracket
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-open-bracket))

(defvar lsp-isar-indent-keyw-close-bracket
  (list "}"))

(defvar lsp-isar-indent--keyw-close-bracket
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-close-bracket))


(defvar lsp-isar-indent-keyw-begin
  (list "begin"))

(defvar lsp-isar-indent--keyw-begin
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-begin))

(defvar lsp-isar-indent-keyw-before-command
  (list "private" "qualified"))

(defvar lsp-isar-indent--keyw-before-command
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-before-command))


(defvar lsp-isar-indent-keyw-proof-script
  (list "supply" "guess" "defer" "prefer" "apply"
	"apply_end" "back" "using" "unfolding"
	;;"subgoal" TODO remove because it changes indentation?
	;;hack
	;; "by" "sorry"
	;; breaks Isar proofs
	))

(defvar lsp-isar-indent--keyw-proof-script
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-proof-script))

(defvar lsp-isar-indent-keyw-prf_asm
  (list "fix" "assume" "presume" "define" "case"))

(defvar lsp-isar-indent--keyw-prf_asm
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-prf_asm))

(defvar lsp-isar-indent-keyw-prf_asm_goal
  (list "obtain" "show" "thus"))

(defvar lsp-isar-indent--keyw-prf_asm_goal
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-prf_asm_goal))

(defvar lsp-isar-indent-keyw-prf_goal
  (list "have" "hence" "consider"))

(defvar lsp-isar-indent--keyw-prf_goal
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-prf_goal))


(defvar lsp-isar-indent-keyw-prf_decl
  (list "using" "unfolding"))

(defvar lsp-isar-indent--keyw-prf_decl
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-prf_decl))

(defvar lsp-isar-indent-keyw-proof
  (append (list "qed" "done" "end" "next" "oops" "proof") lsp-isar-indent-keyw-qed))

(defvar lsp-isar-indent--keyw-proof
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-proof))

;; HACK
(defvar lsp-isar-indent--keyw-proof-hack
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-qed))

(defvar lsp-isar-indent-keyw-HOL-command
  (list "export_code"))

(defvar lsp-isar-indent--keyw-HOL-command
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-HOL-command))

(defvar lsp-isar-indent-keyw-command
  (append lsp-isar-indent-keyw-proof
	  lsp-isar-indent-keyw-quasi-command
	  lsp-isar-indent-keyw-thy_decl
	  lsp-isar-indent-keyw-diag
	  lsp-isar-indent-keyw-thy-goal
	  lsp-isar-indent-thy_decl_block
	  lsp-isar-indent-keyw-prf_asm
	  lsp-isar-indent-keyw-prf_asm_goal
	  lsp-isar-indent-keyw-prf_goal
	  lsp-isar-indent-keyw-prf_decl
	  lsp-isar-indent-keyw-HOL-command))

(defvar lsp-isar-indent-keyw-begin-or-command
  (cons "begin" (cons "subgoal" lsp-isar-indent-keyw-command)))

(defvar lsp-isar-indent--keyw-begin-or-command
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-begin-or-command))

(defvar lsp-isar-indent--keyw-command
  (lsp-isar-indent-create-regex-from-words lsp-isar-indent-keyw-command))

;; looking-at-p can match the next line...
(defun lsp-isar-indent-looking-at-p-nonempty (a)
  (and
   (lsp-isar-indent-current-line-empty-p)
   (/= 0 (lsp-isar-indent-current-line-empty-p))
   (word-at-point)
   (string-match-p a (word-at-point))))

(defun lsp-isar-indent-move-to-first-word-on-the-line ()
  (lsp-isar-indent-trace-indent "lsp-isar-indent-move-to-first-word-on-the-line, initially looking at %s" (word-at-point))
  (back-to-indentation)
  (lsp-isar-indent-trace-indent "lsp-isar-indent-move-to-first-word-on-the-line, now looking at %s" (word-at-point)))

(defun lsp-isar-indent-indent_indent ()
  (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command-open)
      lsp-isar-base-offset
    (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command-close)
	(- lsp-isar-base-offset)
      0)))

(defun lsp-isar-indent-indent_indent_current_line ()
  (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command-open)
      (- lsp-isar-base-offset)
    (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command-close)
	(- lsp-isar-base-offset)
      0)))

(defun lsp-isar-indent-indent_offset ()
  (lsp-isar-indent-move-to-first-word-on-the-line)
  (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof-enclose)
      lsp-isar-base-offset
    0))

(defun lsp-isar-indent-indent_offset_creates_indent ()
  (lsp-isar-indent-move-to-first-word-on-the-line)
  (if (lsp-isar-indent-looking-at-p-nonempty
       (lsp-isar-indent-create-regex-from-words (list "next" "lemma" "theorem" "show" "have"
						      "obtain" "subgoal")))
      lsp-isar-base-offset
    (if (lsp-isar-indent-looking-at-p-nonempty
	 (lsp-isar-indent-create-regex-from-words (list "done" "by")))
	(- lsp-isar-base-offset)
      0)))

(defun lsp-isar-indent-indent_offset_current_line ()
  (lsp-isar-indent-move-to-first-word-on-the-line)
  (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof-enclose)
      (lsp-isar-indent-indent_offset)
    0))

(defun lsp-isar-indent-script_indent ()
  (lsp-isar-indent-move-to-first-word-on-the-line)
  (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof-hack)
      (+ lsp-isar-base-offset)
    0))

(defun lsp-isar-indent-previous-line-with-word ()
  (lsp-isar-indent-trace-indent "lsp-isar-indent-previous-line-with-word, looking at %s" (word-at-point))
  (forward-line -1)
  (let ((finished nil))
    (while (and (not finished)
		(not (= (point) (point-min))))
      (lsp-isar-indent-trace-indent "lsp-isar-indent-previous-line-with-word beginning of line, looking at %s, line %s" (word-at-point)
				    (line-number-at-pos))
      (back-to-indentation) ;; move to first word of the line
      (lsp-isar-indent-trace-indent "lsp-isar-indent-previous-line-with-word, looking at %s, line %s" (word-at-point)
				    (line-number-at-pos))
      (if (word-at-point)
	  (setq finished t)
	(progn
	  (forward-line -1)
	  (beginning-of-line)))))
  (lsp-isar-indent-trace-indent "lsp-isar-indent-previous-line-with-word found, looking at %s, line %s" (word-at-point)
				(line-number-at-pos)))



(defun lsp-isar-indent-indent_brackets ()
  (lsp-isar-indent-trace-indent "lsp-isar-indent-indent_brackets")
  (let ((finished nil)
	(depth 0))
    (save-excursion
      (while (and (not finished) (not (= (point) (point-min))))
	(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-begin-or-command)
	    (setq finished t))
	(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-open-bracket)
	    (setq depth (+ depth lsp-isar-base-offset)))
	(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-close-bracket)
	    (setq depth (- depth lsp-isar-base-offset)))
	(lsp-isar-indent-previous-line-with-word)))
    depth))

(defun lsp-isar-indent-indent_extra ()
  (lsp-isar-indent-trace-indent "lsp-isar-indent-indent_extra")
  (let ((finished nil)
	(depth 0))
    (save-excursion
      (while (and (not finished) (not (= (point) (point-min))))
	(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-begin-or-command)
	    (setq finished t))
	(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-quasi-command)
	    (setq depth lsp-isar-base-offset))
	(lsp-isar-indent-previous-line-with-word)))
    depth))

(defun lsp-isar-indent-indent_structure ()
  (lsp-isar-indent-trace-indent "+++++++\nstarting lsp-isar-indent-indent_structure")
  (let ((finished nil)
	(depth 0))
    ;; TODO only for debugging
    (save-excursion
      (beginning-of-line)
      (lsp-isar-indent-previous-line-with-word)
      (while (and (not finished) (not (= (point) (point-min))))
	(beginning-of-line)
	(progn
	  (lsp-isar-indent-move-to-first-word-on-the-line)
	  (lsp-isar-indent-trace-indent "\tlsp-isar-indent-indent_structure '%s' '%s', indent at: '%s'" (word-at-point) depth (lsp-isar-indent-indent_indent))
	  (setq depth (+ depth (lsp-isar-indent-indent_indent)))
          (lsp-isar-indent-trace-indent "\tlsp-isar-indent-indent_structure %s" depth)
	  (if (and
	       (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-begin-or-command)
	       (not (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof-script)))
	      (progn
		(setq finished t)
                (lsp-isar-indent-trace-indent "\tlsp-isar-indent-indent_structure %s with %s: %s " depth
					      (lsp-isar-indent-indent_offset_creates_indent)
					      (+ depth (lsp-isar-indent-indent_offset_creates_indent)))
		(setq depth (+ depth (current-indentation) (lsp-isar-indent-indent_offset_creates_indent)))
		(lsp-isar-indent-trace-indent "\tlsp-isar-indent-indent_structure set to %s" depth))
	    (lsp-isar-indent-previous-line-with-word))))
      (lsp-isar-indent-trace-indent "\tlsp-isar-indent-indent_structure final: %s" depth)
      depth)))

(defun lsp-isar-indent-goto-previous-line-with-command ()
  (lsp-isar-indent-trace-indent "lsp-isar-indent-goto-previous-line-with-command")
  (let ((finished nil))
    (while (and (not finished) (not (= (point) (point-min))))
      (lsp-isar-indent-move-to-first-word-on-the-line)
      (lsp-isar-indent-trace-indent "lsp-isar-indent-goto-previous-line-with-command: %s" (word-at-point))
      (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-begin-or-command)
	  (setq finished t)
	(lsp-isar-indent-previous-line-with-word)))))

(defun lsp-isar-indent-indentation_depth (lsp-isar-indent-indent_structure lsp-isar-indent-indent_brackets)
  (lsp-isar-indent-trace-indent "+++++++++\nlsp-isar-indent-indentation_depth")
  (save-excursion
    (lsp-isar-indent-move-to-first-word-on-the-line)
    (lsp-isar-indent-trace-indent "\tlsp-isar-indent-indentation_depth, init word: %s, command? %s" (word-at-point)
				  (and (word-at-point) (string-match-p lsp-isar-indent--keyw-begin-or-command (word-at-point))))
    (if (and (lsp-isar-indent-current-line-empty-p)
	     (/= 0 (lsp-isar-indent-current-line-empty-p))
	     (looking-at "[[:word:]]")
	     (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command))
	(if (or
	     (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-begin)
	     (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-before-command)
	     (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-theory))
	    0
	  (if (or (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof-enclose_not_done))
              (progn
		(lsp-isar-indent-trace-indent "\tcommand enclose")
		(- lsp-isar-indent-indent_structure (lsp-isar-indent-indent_offset_current_line)))
	    (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof)
		(progn
		  (lsp-isar-indent-trace-indent "\tcommand proof %s %s %s" lsp-isar-indent-indent_structure
						(lsp-isar-indent-script_indent)
						(lsp-isar-indent-indent_offset))
		  (max (+ lsp-isar-indent-indent_structure (lsp-isar-indent-indent_indent_current_line) 0;; (- (lsp-isar-indent-indent_offset))
			  )
		       0))
	      (progn
		(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command)
		    (progn
		      (lsp-isar-indent-trace-indent "\tcommand")
		      (+ lsp-isar-indent-indent_structure (- (lsp-isar-indent-indent_offset))))
		  (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-proof-enclose)
		      (progn
			(lsp-isar-indent-trace-indent "\tlsp-isar-indent--keyw-proof-enclose")
			(max (- lsp-isar-indent-indent_structure lsp-isar-base-offset) lsp-isar-base-offset))
		    (progn
		      (lsp-isar-indent-trace-indent "\tcommand+no enclose")
		      (let ((curr_quasi (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-quasi-command)))
		        (lsp-isar-indent-goto-previous-line-with-command)
			(lsp-isar-indent-move-to-first-word-on-the-line)
			(let* ((prev_quasi (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-quasi-command))
			       (extra
				(if (or (and curr_quasi prev_quasi)
					(and (not curr_quasi) (not prev_quasi)))
				    0
				  (if (or (and curr_quasi (not prev_quasi)))
				      (- (lsp-isar-indent-indent_extra))
				    (lsp-isar-indent-indent_extra)))))
			  (lsp-isar-indent-trace-indent "\textra %s %s %s" extra prev_quasi curr_quasi)
			  (+ lsp-isar-indent-indent_structure lsp-isar-indent-indent_brackets extra (- (lsp-isar-indent-indent_offset))))))))))))
      ;; no command at the head
      (progn
	(lsp-isar-indent-trace-indent "\tlsp-isar-indent-indentation_depth/no command")
	(lsp-isar-indent-trace-indent "\tword at point: %s" (word-at-point))
	(lsp-isar-indent-goto-previous-line-with-command)
	(lsp-isar-indent-trace-indent "\tword at point: %s" (word-at-point))
	(lsp-isar-indent-trace-indent "\tindent-indent: %s; lsp-isar-indent-indent_offset: %s; command: %s"  (lsp-isar-indent-indent_indent)
				      (lsp-isar-indent-indent_offset) (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command))
	(if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-command)
	    (+ lsp-isar-indent-indent_structure lsp-isar-indent-indent_brackets lsp-isar-base-offset
	       (- (lsp-isar-indent-indent_indent)) (- (lsp-isar-indent-indent_offset)))
	  (let ((extra (if (lsp-isar-indent-looking-at-p-nonempty lsp-isar-indent--keyw-quasi-command) (lsp-isar-indent-indent_extra) 0)))
	    (lsp-isar-indent-trace-indent "\tlsp-isar-indent-indent_structure: %s; lsp-isar-indent-indent_brackets: %s; extra: %s; lsp-isar-indent-indent_offset: %s"
					  lsp-isar-indent-indent_structure lsp-isar-indent-indent_brackets extra lsp-isar-base-offset)
	    (+ lsp-isar-indent-indent_structure lsp-isar-indent-indent_brackets extra lsp-isar-base-offset)))))))

(defun lsp-isar-indent-line ()
  "Indent current line as Isar code"
  (interactive)
  (beginning-of-line)
  (lsp-isar-indent-trace-indent "************************")
  (let* ((cur-struct-indent (lsp-isar-indent-indent_structure))
	 (cur-bracket-indent (lsp-isar-indent-indent_brackets))
	 (cur-indent (max 0 (lsp-isar-indent-indentation_depth cur-struct-indent cur-bracket-indent))))
    ;;(if cur-indent
    ;;(indent-line-to cur-indent)
    (lsp-isar-indent-trace-indent "cur-struct-indent: %s" cur-struct-indent)
    (lsp-isar-indent-trace-indent "cur-bracket-indent: %s" cur-bracket-indent)
    (lsp-isar-indent-trace-indent "cur-indent: %s" cur-indent)
    (indent-line-to cur-indent)))


(provide 'lsp-isar-indent)

;;; lsp-isar-indent.el ends here

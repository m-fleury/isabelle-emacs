;;; -*- lexical-binding: t; -*-

;; Copyright (C) 2018 Mathias Fleury

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

;;; Code:

(defun current-line-empty-p ()
  (or (not (thing-at-point 'line)) (string-match-p "^\\s-*$" (thing-at-point 'line))))

(defun create-regex-from-words (s)
  (concat
   (cl-reduce (lambda (w y) (concat w "\\|" y))
  (mapcar (lambda (w) (concat "\\(" w "\\)")) s)))
  )

(defvar lsp-isar-keyw-quasi-command
      (list
       "and" "assumes" "constrains" "defines" "fixes" "for" "if" "includes" "notes" "rewrites"
       "obtains" "shows" "when" "where" "imports" "theory" "datatype")) ;; missing "|"

(defvar lsp-isar--keyw-quasi-command
      (create-regex-from-words lsp-isar-keyw-quasi-command))

(defvar lsp-isar-keyw-command-open
      (list "begin" "proof"))

(defvar lsp-isar--keyw-command-open
      (create-regex-from-words lsp-isar-keyw-command-open))

(defvar lsp-isar-keyw-command-close
      (list "qed" "end"))

(defvar lsp-isar--keyw-command-close
      (create-regex-from-words lsp-isar-keyw-command-close))

(defvar lsp-isar-keyw-theory
      (list "theory" "imports" "end" "begin"))

(defvar lsp-isar--keyw-theory
      (create-regex-from-words lsp-isar-keyw-theory))

(defvar lsp-isar-trace-indent t)


(defun lsp-isar-trace-indent (&rest args)
  (if lsp-isar-trace-indent
    (apply 'message args)))

(defvar lsp-isar-keyw-diag
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

(defvar lsp-isar--keyw-diag
      (create-regex-from-words lsp-isar-keyw-diag))

(defvar lsp-isar-keyw-thy_decl
      (list
       "default_sorts" "typedecl" "type_synonym" "nonterminal" "judgement"
       "typedecl" "type_synonym" "nonterminal" "judgment"
       "consts" "syntax" "no_syntax" "translations" "no_translations"
       "definition" "abbreviation" "type_notation" "no_type_notation" "notation"
       "no_notation" "axiomatization" "alias" "type_alias" "lemmas" "declare"
       "hide_class" "hide_type" "hide_const" "hide_fact"))

(defvar lsp-isar--keyw-thy_decl
      (create-regex-from-words lsp-isar-keyw-thy_decl))

(defvar lsp-isar-keyw-thy-goal
      (list "theorem" "lemma" "corollary" "proposition"))

(defvar lsp-isar--keyw-thy-goal
      (create-regex-from-words lsp-isar-keyw-thy-goal))

(defvar lsp-isar-thy_decl_block
      (list "context" "locale" "experiment"
	      "bundle" "instantiation" "overloading"
	      "notepad"))

(defvar lsp-isar--keyw-thy_decl
      (create-regex-from-words lsp-isar-keyw-thy_decl))

(defvar indent_offset 2)

(defvar lsp-isar-keyw-qed
      (list "by" "\\.\\." "\\." "sorry" "\\\\<proof>"))

(defvar lsp-isar--keyw-qed
      (create-regex-from-words lsp-isar-keyw-qed))

(defvar lsp-isar-keyw-proof-enclose
      (list "qed" "done" "end" "next" "subgoal"))

(defvar lsp-isar--keyw-proof-enclose
      (create-regex-from-words lsp-isar-keyw-proof-enclose))

(defvar lsp-isar-keyw-proof-enclose_not_done
      (list "qed" "end" "next"))

(defvar lsp-isar--keyw-proof-enclose_not_done
      (create-regex-from-words lsp-isar-keyw-proof-enclose_not_done))

(defvar lsp-isar-keyw-open-bracket
      (list "{"))

(defvar lsp-isar--keyw-open-bracket
      (create-regex-from-words lsp-isar-keyw-open-bracket))

(defvar lsp-isar-keyw-close-bracket
      (list "}"))

(defvar lsp-isar--keyw-close-bracket
      (create-regex-from-words lsp-isar-keyw-close-bracket))


(defvar lsp-isar-keyw-begin
      (list "begin"))

(defvar lsp-isar--keyw-begin
      (create-regex-from-words lsp-isar-keyw-begin))

(defvar lsp-isar-keyw-before-command
      (list "private" "qualified"))

(defvar lsp-isar--keyw-before-command
      (create-regex-from-words lsp-isar-keyw-before-command))


(defvar lsp-isar-keyw-proof-script
      (list "supply" "guess" "defer" "prefer" "apply"
	    "apply_end" "back" "using" "unfolding"
	    ;;"subgoal" TODO remove because it changes indentation?
	    ;;hack
	    ;; "by" "sorry"
	    ;; breaks Isar proofs
	    ))

(defvar lsp-isar--keyw-proof-script
      (create-regex-from-words lsp-isar-keyw-proof-script))

(defvar lsp-isar-keyw-prf_asm
      (list "fix" "assume" "presume" "define" "case"))

(defvar lsp-isar--keyw-prf_asm
      (create-regex-from-words lsp-isar-keyw-prf_asm))

(defvar lsp-isar-keyw-prf_asm_goal
      (list "obtain" "show" "thus"))

(defvar lsp-isar--keyw-prf_asm_goal
      (create-regex-from-words lsp-isar-keyw-prf_asm_goal))

(defvar lsp-isar-keyw-prf_goal
      (list "have" "hence" "consider"))

(defvar lsp-isar--keyw-prf_goal
      (create-regex-from-words lsp-isar-keyw-prf_goal))


(defvar lsp-isar-keyw-prf_decl
      (list "using" "unfolding"))

(defvar lsp-isar--keyw-prf_decl
      (create-regex-from-words lsp-isar-keyw-prf_decl))

(defvar lsp-isar-keyw-proof
      (append (list "qed" "done" "end" "next" "oops" "proof") lsp-isar-keyw-qed
	      ))

(defvar lsp-isar--keyw-proof
      (create-regex-from-words lsp-isar-keyw-proof))

;; HACK
(defvar lsp-isar--keyw-proof-hack
      (create-regex-from-words lsp-isar-keyw-qed))

(defvar lsp-isar-keyw-HOL-command
      (list "export_code"))

(defvar lsp-isar--keyw-HOL-command
      (create-regex-from-words lsp-isar-keyw-HOL-command))

(defvar lsp-isar-keyw-command
      (append lsp-isar-keyw-proof
	      lsp-isar-keyw-quasi-command
	      lsp-isar-keyw-thy_decl
	      lsp-isar-keyw-diag
	      lsp-isar-keyw-thy-goal
	      lsp-isar-thy_decl_block
	      lsp-isar-keyw-prf_asm
	      lsp-isar-keyw-prf_asm_goal
	      lsp-isar-keyw-prf_goal
	      lsp-isar-keyw-prf_decl
	      lsp-isar-keyw-HOL-command
	      ))

(defvar lsp-isar-keyw-begin-or-command
      (cons "begin" (cons "subgoal" lsp-isar-keyw-command)))

(defvar lsp-isar--keyw-begin-or-command
      (create-regex-from-words lsp-isar-keyw-begin-or-command))

(defvar lsp-isar--keyw-command
      (create-regex-from-words lsp-isar-keyw-command))

;; looking-at-p can match the next line...
(defun looking-at-p-nonempty (a)
  (and
   (current-line-empty-p)
   (/= 0 (current-line-empty-p))
   (word-at-point)
   (string-match-p a (word-at-point))))

(defun move-to-first-word-on-the-line ()
  (lsp-isar-trace-indent "move-to-first-word-on-the-line, initially looking at %s" (word-at-point))
  (back-to-indentation)
  (lsp-isar-trace-indent "move-to-first-word-on-the-line, now looking at %s" (word-at-point)))

(defun indent_indent ()
  (if (looking-at-p-nonempty lsp-isar--keyw-command-open)
      indent_offset
    (if (looking-at-p-nonempty lsp-isar--keyw-command-close)
	(- indent_offset)
      0)))

(defun indent_indent_current_line ()
  (if (looking-at-p-nonempty lsp-isar--keyw-command-open)
      (- indent_offset)
    (if (looking-at-p-nonempty lsp-isar--keyw-command-close)
	(- indent_offset)
      0)))

(defun indent_offset ()
  (move-to-first-word-on-the-line)
  (if (looking-at-p-nonempty lsp-isar--keyw-proof-enclose)
      indent_offset
    0))

(defun indent_offset_creates_indent ()
  (move-to-first-word-on-the-line)
  (if (looking-at-p-nonempty
       (create-regex-from-words (list "next" "lemma" "theorem" "show" "have"
				      "obtain" "subgoal")))
      indent_offset
    (if (looking-at-p-nonempty
	 (create-regex-from-words (list "done" "by")))
	(- indent_offset)
      0)))

(defun indent_offset_current_line ()
  (move-to-first-word-on-the-line)
  (if (looking-at-p-nonempty lsp-isar--keyw-proof-enclose)
      (indent_offset)
    0))

(defun script_indent ()
  (move-to-first-word-on-the-line)
  (if (looking-at-p-nonempty lsp-isar--keyw-proof-hack)
      (+ indent_offset)
    0))

(defun previous-line-with-word ()
  (lsp-isar-trace-indent "previous-line-with-word, looking at %s" (word-at-point))
  (forward-line -1)
  (let ((finished nil))
    (while (and (not finished)
		(not (= (point) (point-min))))
      (lsp-isar-trace-indent "previous-line-with-word beginning of line, looking at %s, line %s" (word-at-point)
			     (line-number-at-pos))
      (back-to-indentation) ;; move to first word of the line
      (lsp-isar-trace-indent "previous-line-with-word, looking at %s, line %s" (word-at-point)
			     (line-number-at-pos))
      (if (word-at-point)
	  (setq finished t)
	(progn
	  (forward-line -1)
	  (beginning-of-line)))))
  (lsp-isar-trace-indent "previous-line-with-word found, looking at %s, line %s" (word-at-point)
			 (line-number-at-pos)))



(defun indent_brackets ()
  (lsp-isar-trace-indent "indent_brackets")
  (setq finished nil)
  (save-excursion
    (setq depth 0)
    (while (and (not finished) (not (= (point) (point-min))))
      (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	  (setq finished t))
      (if (looking-at-p-nonempty lsp-isar--keyw-open-bracket)
	  (setq depth (+ depth indent_offset)))
      (if (looking-at-p-nonempty lsp-isar--keyw-close-bracket)
	  (setq depth (- depth indent_offset)))
      (previous-line-with-word)
      ))
  depth)

(defun indent_extra ()
  (lsp-isar-trace-indent "indent_extra")
  (setq finished nil)
  (setq depth 0)
  (save-excursion
    (while (and (not finished) (not (= (point) (point-min))))
      (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	  (setq finished t))
      (if (looking-at-p-nonempty lsp-isar--keyw-quasi-command)
	  (setq depth indent_offset))
      (previous-line-with-word)))
  depth)

(defun indent_structure ()
  (lsp-isar-trace-indent "+++++++\nstarting indent_structure")
  (interactive)
  (setq finished nil)
  ;; TODO only for debugging
  (save-excursion
    (beginning-of-line)
    (previous-line-with-word)
    (setq depth 0)
    (while (and (not finished) (not (= (point) (point-min))))
      (beginning-of-line)
      (if (not (looking-at "[[:word:]]"));; if there is no word, skip line, e.g. "}"
	  (previous-line-with-word)
	(progn
	  (move-to-first-word-on-the-line)
	  (lsp-isar-trace-indent "\tindent_structure '%s' '%s', indent at: '%s'" (word-at-point) depth (indent_indent))
	  (setq depth (+ depth (indent_indent)))
          (lsp-isar-trace-indent "\tindent_structure %s" depth)
	  (if (and
	       (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	       (not (looking-at-p-nonempty lsp-isar--keyw-proof-script)))
	      (progn
		(setq finished t)
                (lsp-isar-trace-indent "\tindent_structure %s with %s: %s " depth
				       (indent_offset_creates_indent)
				       (+ depth (indent_offset_creates_indent)))
		(setq depth (+ depth (current-indentation) (indent_offset_creates_indent)))
		(lsp-isar-trace-indent "\tindent_structure set to %s" depth))
	    (previous-line-with-word)))))
    (lsp-isar-trace-indent "\tindent_structure final: %s" depth)
    depth))

(defun goto-prev-line-command ()
  (lsp-isar-trace-indent "goto-prev-line-command")
  (setq finished nil)
  (while (and (not finished) (not (= (point) (point-min))))
    (move-to-first-word-on-the-line)
    (lsp-isar-trace-indent "goto-prev-line-command: %s" (word-at-point))
    (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	(setq finished t)
      (previous-line-with-word)))
  depth)

(defun indentation_depth (indent_structure indent_brackets)
  (lsp-isar-trace-indent "+++++++++\nindentation_depth")
  (save-excursion
    (move-to-first-word-on-the-line)
    (lsp-isar-trace-indent "\tindentation_depth, init word: %s, command? %s" (word-at-point)
	     (and (word-at-point) (string-match-p lsp-isar--keyw-begin-or-command (word-at-point))))
    (if (and (current-line-empty-p)
	     (/= 0 (current-line-empty-p))
	     (looking-at "[[:word:]]"))
	(if (or
	     (looking-at-p-nonempty lsp-isar--keyw-begin)
	     (looking-at-p-nonempty lsp-isar--keyw-before-command)
	     (looking-at-p-nonempty lsp-isar--keyw-theory))
	    0
	  (if (or (looking-at-p-nonempty lsp-isar--keyw-proof-enclose_not_done))
              (progn
		(lsp-isar-trace-indent "\tcommand enclose")
		(- indent_structure (indent_offset_current_line)))
	    (if (looking-at-p-nonempty lsp-isar--keyw-proof)
		(progn
		  (lsp-isar-trace-indent "\tcommand proof %s %s %s" indent_structure
					 (script_indent)
					 (indent_offset))
		  (max (+ indent_structure (indent_indent_current_line) 0;; (- (indent_offset))
			  )
		       0))
	      (progn
		(if (looking-at-p-nonempty lsp-isar--keyw-command)
		    (progn
		      (lsp-isar-trace-indent "\tcommand")
		      (+ indent_structure (- (indent_offset))))
		  (if (looking-at-p-nonempty lsp-isar--keyw-proof-enclose)
		      (progn
			(lsp-isar-trace-indent "\tlsp-isar--keyw-proof-enclose")
			(max (- indent_structure indent_offset) indent_offset))
		    (progn
		      (lsp-isar-trace-indent "\tcommand+no enclose")
		      (let ((curr_quasi (looking-at-p-nonempty lsp-isar--keyw-quasi-command)))
		        (goto-prev-line-command)
			(move-to-first-word-on-the-line)
			(let* ((prev_quasi (looking-at-p-nonempty lsp-isar--keyw-quasi-command))
			       (extra
				(if (or (and curr_quasi prev_quasi)
					(and (not curr_quasi) (not prev_quasi)))
				    0
				  (if (or (and curr_quasi (not prev_quasi)))
				      (- (indent_extra))
				    (indent_extra)))))
			  (lsp-isar-trace-indent "\textra %s %s %s" extra prev_quasi curr_quasi)
			  (+ indent_structure indent_brackets extra (- (indent_offset))))))))))))
      ;; no command at the head
      (progn
	(lsp-isar-trace-indent "\tindentation_depth/no command")
	(lsp-isar-trace-indent "\tword at point: %s" (word-at-point))
	(goto-prev-line-command)
	(lsp-isar-trace-indent "\tword at point: %s" (word-at-point))
	(lsp-isar-trace-indent "\tindent-indent: %s; indent_offset: %s; command: %s"  (indent_indent)
		 (indent_offset) (looking-at-p-nonempty lsp-isar--keyw-command))
	(if (looking-at-p-nonempty lsp-isar--keyw-command)
	    (+ indent_structure indent_brackets indent_offset
	       (- (indent_indent)) (- (indent_offset)))
	  (let ((extra (if (looking-at-p-nonempty lsp-isar--keyw-quasi-command) (indent_extra) 0)))
	    (lsp-isar-trace-indent "\tindent_structure: %s; indent_brackets: %s; extra: %s; indent_offset: %s"
		     indent_structure indent_brackets extra indent_offset)
	    (+ indent_structure indent_brackets extra indent_offset)))))))

(defun lsp-isar-indent-line ()
  "Indent current line as Isar code"
  (interactive)
  (beginning-of-line)
  (lsp-isar-trace-indent "************************")
  (let* (
	 (cur-struct-indent (indent_structure))
	 (cur-bracket-indent (indent_brackets))
	 (cur-indent (max 0 (indentation_depth cur-struct-indent cur-bracket-indent))))
    ;;(if cur-indent
    ;;(indent-line-to cur-indent)
    (lsp-isar-trace-indent "cur-struct-indent: %s" cur-struct-indent)
    (lsp-isar-trace-indent "cur-bracket-indent: %s" cur-bracket-indent)
    (lsp-isar-trace-indent "cur-indent: %s" cur-indent)
    (indent-line-to cur-indent)))


(provide 'lsp-indent)

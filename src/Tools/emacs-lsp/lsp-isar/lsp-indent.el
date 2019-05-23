(defun current-line-empty-p ()
  (string-match-p "^\\s-*$" (thing-at-point 'line)))

(setq lsp-isar-keyw-quasi-command
      (concat
       "and\\|assumes\\|constrains\\|defines\\|fixes\\|for\\|if\\|includes\\|notes\\|rewrites\\|"
       "obtains\\|shows\\|when\\|where")) ;; missing "|"

(setq lsp-isar--keyw-quasi-command
      (concat "^[ \t]*\\(" lsp-isar-keyw-quasi-command "\\)"))

(setq lsp-isar-keyw-command-open
      "begin\\|proof")

(setq lsp-isar--keyw-command-open
      (concat "^[ \t]*\\(" lsp-isar-keyw-command-open "\\)"))

(setq lsp-isar-keyw-command-close
      "qed\\|end")

(setq lsp-isar--keyw-command-close
      (concat "^[ \t]*\\(" lsp-isar-keyw-command-close "\\)"))

(setq lsp-isar-keyw-theory
      "theory\\|imports\\|end\\|begin")

(setq lsp-isar--keyw-theory
      (concat "^[ \t]*\\(" lsp-isar-keyw-theory "\\)"))

(setq lsp-isar-keyw-diag
      (concat
       "export_generated_files\\|ML_val\\|ML_command\\|print_bundles\\|help\\|"
       "print_commands\\|print_options\\|print_context\\|print_theory\\|print_definitions\\|"
       "print_syntax\\|print_abbrevs\\|print_defn_rules\\|print_theorems\\|print_locales\\|"
       "print_classes\\|print_locale\\|print_interps\\|print_dependencies\\|print_attributes\\|"
       "print_simpset\\|print_rules\\|print_trans_rules\\|print_methods\\|"
       "print_antiquotations\\|print_ML_antiquotations\\|thy_deps\\|locale_deps\\|class_deps\\|"
       "thm_deps\\|print_term_bindings\\|print_facts\\|print_cases\\|print_statement\\|thm\\|prf\\|"
       "full_prf\\|prop\\|term\\|typ\\|print_codesetup\\|unused_thms\\|print_state\\|welcome\\|"
       "find_theorems\\|find_consts"))

(setq lsp-isar--keyw-diag
      (concat "^[ \t]*\\(" lsp-isar-keyw-diag "\\)"))

(setq lsp-isar-keyw-thy_decl
      (concat
       "default_sorts\\|typedecl\\|type_synonym\\|nonterminal\\|judgement\\|"
       "typedecl\\|" "type_synonym\\|" "nonterminal\\|" "judgment\\|"
       "consts\\|" "syntax\\|" "no_syntax\\|" "translations\\|" "no_translations\\|"
       "definition\\|" "abbreviation\\|" "type_notation\\|" "no_type_notation\\|" "notation\\|"
       "no_notation\\|" "axiomatization\\|" "alias\\|" "type_alias\\|" "lemmas\\|" "declare\\|"
       "hide_class\\|" "hide_type\\|" "hide_const\\|" "hide_fact"))

(setq lsp-isar--keyw-thy_decl
      (concat "^[ \t]*\\(" lsp-isar-keyw-thy_decl "\\)"))

(setq lsp-isar-keyw-thy-goal
      (concat "theorem\\|" "lemma\\|" "corollary\\|" "proposition"))

(setq lsp-isar--keyw-thy-goal
      (concat "^[ \t]*\\(" lsp-isar-keyw-thy-goal "\\)"))

(setq lsp-isar-thy_decl_block
      (concat "context\\|" "locale\\|" "experiment\\|"
	      "bundle\\|" "instantiation\\|" "overloading\\|"
	      "notepad"))

(setq lsp-isar--keyw-thy_decl
      (concat "^[ \t]*\\(" lsp-isar-keyw-thy_decl "\\)"))

(setq indent_offset 2)

(setq lsp-isar-keyw-proof-enclose
      "qed\\|done\\|end\\|next")

(setq lsp-isar--keyw-proof-enclose
      (concat "^[ \t]*\\(" lsp-isar-keyw-proof-enclose "\\)"))

(setq lsp-isar-keyw-open-bracket
      "{")

(setq lsp-isar--keyw-open-bracket
      (concat "^[ \t]*\\(" lsp-isar-keyw-open-bracket "\\)"))

(setq lsp-isar-keyw-close-bracket
      "{")

(setq lsp-isar--keyw-close-bracket
      (concat "^[ \t]*\\(" lsp-isar-keyw-close-bracket "\\)"))


(setq lsp-isar-keyw-begin
      (concat "begin"))

(setq lsp-isar--keyw-begin
      (concat "^[ \t]*\\(" lsp-isar-keyw-begin "\\)"))

(setq lsp-isar-keyw-before
      (concat "private\\|qualified"))

(setq lsp-isar--keyw-before
      (concat "^[ \t]*\\(" lsp-isar-keyw-before "\\)"))


(setq lsp-isar-keyw-proof-script
      (concat "supply\\|guess\\|defer\\|prefer\\|apply\\|"
	      "apply_end\\|subgoal\\|back"))

(setq lsp-isar--keyw-proof-script
      (concat "^[ \t]*\\(" lsp-isar-keyw-proof-script "\\)"))

(setq lsp-isar-keyw-prf_asm
      (concat "fix\\|assume\\|presume\\|define\\|case"))

(setq lsp-isar--keyw-prf_asm
      (concat "^[ \t]*\\(" lsp-isar-keyw-prf_asm "\\)"))

(setq lsp-isar-keyw-prf_asm_goal
      (concat "obtain\\|show\\|thus"))

(setq lsp-isar--keyw-prf_asm_goal
      (concat "^[ \t]*\\(" lsp-isar-keyw-prf_asm_goal "\\)"))

(setq lsp-isar-keyw-prf_goal
      (concat "have\\|hence\\|consider"))

(setq lsp-isar--keyw-prf_goal
      (concat "^[ \t]*\\(" lsp-isar-keyw-prf_goal "\\)"))


(setq lsp-isar-keyw-prf_decl
      (concat "using\\|unfolding"))

(setq lsp-isar--keyw-prf_goal
      (concat "^[ \t]*\\(" lsp-isar-keyw-prf_decl "\\)"))

(setq lsp-isar-keyw-proof
      "qed\\|done\\|end\\|next\\|oops\\|proof")

(setq lsp-isar--keyw-proof
      (concat "^[ \t]*\\("
	      lsp-isar-keyw-proof
	      "\\)"))

(setq lsp-isar-keyw-qed
      "by\\|..\\|.\\|sorry\\|\\\\<proof>")

(setq lsp-isar--keyw-qed
      (concat "^[ \t]*\\("
	      lsp-isar-keyw-qed
	      "\\)"))


(setq lsp-isar-keyw-command
      (concat lsp-isar-keyw-proof "\\|"
	      lsp-isar-keyw-quasi-command "\\|"
	      lsp-isar-keyw-thy_decl "\\|"
	      lsp-isar-keyw-diag "\\|"
	      lsp-isar-keyw-thy-goal "\\|"
	      lsp-isar-thy_decl_block "\\|"
	      lsp-isar-keyw-prf_asm "\\|"
	      lsp-isar-keyw-prf_asm_goal "\\|"
	      lsp-isar-keyw-prf_decl "\\|"
	      lsp-isar-keyw-prf_goal))

(setq lsp-isar-keyw-begin-or-command
      (concat "begin\\|"
	       lsp-isar-keyw-command))

(setq lsp-isar--keyw-begin-or-command
      (concat "^[ \t]*\\("
	      lsp-isar-keyw-begin-or-command
	      "\\)"))

(setq lsp-isar--keyw-command
      (concat "^[ \t]*\\("
	      lsp-isar-keyw-begin-or-command
	      "\\)"))

;; looking-at-p can match the next line...
(defun looking-at-p-nonempty (a)
  (and
   (/= 0 (current-line-empty-p))
   (looking-at-p a)))

(defun indent_indent ()
  (if (looking-at-p-nonempty lsp-isar--keyw-command-open)
      indent_offset
    (if (looking-at-p-nonempty lsp-isar--keyw-command-close)
	(- indent_offset)
      0)))

(defun indent_offset ()
  (if (looking-at-p-nonempty lsp-isar--keyw-command)
      indent_offset
    0))

(defun indent_brackets ()
  (message "indent_brackets")
  (setq finished nil)
  (setq depth 0)
  (save-excursion
    (while (and (not finished) (not (= (point) (point-min))))
      (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	  (setq finished t))
      (if (looking-at-p-nonempty lsp-isar--keyw-open-bracket)
	  (setq depth (+ depth indent_offset)))
      (if (looking-at-p-nonempty lsp-isar--keyw-close-bracket)
	  (setq depth (- depth indent_offset)))
      (forward-line -1)))
  depth)

(defun indent_extra ()
  (message "indent_extra")
  (setq finished nil)
  (setq depth 0)
  (save-excursion
    (while (and (not finished) (not (= (point) (point-min))))
      (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	  (setq finished t))
      (if (looking-at-p-nonempty lsp-isar--keyw-quasi-command)
	  (setq depth indent_offset))
      (forward-line -1)))
  depth)

(defun indent_structure ()
  (message "indent_structure")
  (interactive)
  (setq finished nil)
  (setq depth 0)
  ;; TODO only for debugging
  (beginning-of-line)
  (save-excursion
    (while (and (not finished) (not (= (point) (point-min))))
      (message "indent_structure %s %s, indent at: %s" (word-at-point) depth (indent_indent))
      (setq depth (+ depth (indent_indent)))
      (if (and
	   (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	   (not (looking-at-p-nonempty lsp-isar--keyw-proof-script)))
	  (progn
	    (setq finished t)
	    (setq depth (+ depth (indent_offset)
			   ;;(current-indentation)
			   ))))
      (forward-line -1)))
  (message "indent_structure %s" depth)
  depth)

(defun goto-prev-line-command ()
  (message "goto-prev-line-command")
  (setq finished nil)
  (while (and (not finished) (not (= (point) (point-min))))
    (message "%s" (thing-at-point 'line))
    (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	(setq finished t))
    (forward-line -1))
  depth)

(defun indentation_depth (indent_structure indent_brackets)
  (message "indentation_depth")
  (save-excursion
    (if (looking-at-p-nonempty lsp-isar--keyw-begin-or-command)
	(if (or
	     (looking-at-p-nonempty lsp-isar--keyw-begin)
	     (looking-at-p-nonempty lsp-isar--keyw-before)
	     (looking-at-p-nonempty lsp-isar--keyw-theory))
	    0
	  (if (looking-at-p-nonempty lsp-isar--keyw-proof-enclose)
              (progn
		(message "command enclose")
		(- indent_structure indent_offset))
	    (if (looking-at-p-nonempty lsp-isar--keyw-proof)
		(progn
		  (message "command proof")
		  (max (- indent_structure indent_offset) indent_offset))
	      (progn
		(if (and nil
			 (looking-at-p-nonempty lsp-isar--keyw-command))
		    (progn
		      (message "command")
		      (- indent_structure indent_offset))
		  (if (looking-at-p-nonempty lsp-isar--keyw-proof-enclose)
		      (max (- indent_structure indent_offset) indent_offset)
		    (progn
		      (message "command+no enclose")
		      (let ((curr_quasi (looking-at-p-nonempty lsp-isar--keyw-quasi-command)))
			(forward-line -1)
			(let* ((prev_quasi (looking-at-p-nonempty lsp-isar--keyw-quasi-command))
			       (extra
				(if (or (and curr_quasi prev_quasi)
					(and (not curr_quasi) (not prev_quasi)))
				    0
				  (if (or (and curr_quasi (not prev_quasi)))
				      (- (indent_extra))
				    ((indent_extra))))))
			  (message "%s" extra)
			  (+ indent_structure indent_brackets extra (- indent_offset)))))))))))
      ;; no command at the head
      (progn
	(message "indentation_depth/no command")
	(goto-prev-line-command)
	(message "word at point: %s" (word-at-point))
	(message "indent-indent: %s; (indent_offset): %s; command: %s"  (indent_indent)
		 (indent_offset) (looking-at-p-nonempty lsp-isar--keyw-command))
	(if (looking-at-p-nonempty lsp-isar--keyw-command)
	    (+ indent_structure indent_brackets indent_offset
	       (- (indent_indent)) (- (indent_offset)))
	  (let ((extra (if (looking-at-p-nonempty lsp-isar--keyw-quasi-command) (indent_extra) 0)))
	    (+ indent_structure indent_brackets extra indent_offset)))))))

(defun isar-indent-line ()
  "Indent current line as Isar code"
  (interactive)
  (beginning-of-line)
  (let* (
	 (cur-struct-indent (indent_structure))
	 (cur-bracket-indent (indent_brackets))
	 (cur-indent (indentation_depth cur-struct-indent cur-bracket-indent )))
    ;;(if cur-indent
    ;;(indent-line-to cur-indent)
    (message "cur-struct-indent: %s" cur-struct-indent)
    (message "cur-bracket-indent: %s" cur-bracket-indent)
    (message "cur-indent: %s" cur-indent))
  t)
;;(indent-line-to 0))))
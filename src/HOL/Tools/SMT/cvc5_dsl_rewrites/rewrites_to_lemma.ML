signature WRITE_LEMMA =
sig
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

  val write_lemma: PARSE_REWRITE.rewrite_tree ->  Proof.context -> string list list (*For now can I do this smarter?*)
  val write_lemmas: PARSE_REWRITE.rewrite_tree list -> string -> string -> Proof.context -> string list list (*For now can I do this smarter?*)

  (*val write_file:  PARSE_REWRITE.rewrite_tree list -> string list*)
end;

open PARSE_REWRITE
open SMTLIB_Proof

structure WRITE_LEMMA: WRITE_LEMMA =
struct
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

fun string_of_term ctxt s =
  let
    val t = Syntax.read_term ctxt s;
    val T = Term.type_of t;
    val ctxt' = Proof_Context.augment t ctxt;
  in
    Pretty.string_of
      (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)])
  end;

fun get_term tree ctxt = Syntax.string_of_term ctxt (fst (SMTLIB_Proof.term_of tree (empty_context ctxt Symtab.empty Symtab.empty)))

fun write_file_header theory_name theory_imports= [["theory " ^ theory_name ^ "\n"],["  imports " ^ theory_imports ^ "\n"], ["begin\n\n"]]
val write_file_footer = ["end"]

fun write_lemma_header name = ["lemma " ^ name ^ ":\n"]
fun write_fixes pars ctxt = 
let
  val cx = (empty_context ctxt Symtab.empty Symtab.empty)
  fun write_par (SMTLIB.S [var,typ]) = SMTLIB.str_of var ^ "::" ^ Syntax.string_of_typ ctxt (SMTLIB_Proof.type_of cx typ)
  fun write_params [] = [] |
  write_params (p::ps) = write_par p ^ (if ps = [] then "" else " and ") :: write_params ps
in
  ["  fixes " ] @ write_params pars @ ["\n"]
end
fun write_shows match target ctxt = ["  shows \"((" ^ get_term match ctxt ^ ") = (" ^ get_term target ctxt ^ "))\"\n" ] (*Use term_of? and then parse to string? Need context*)
fun write_shows_wth_assump ass match target ctxt
   =  ["  shows (" ^ get_term ass ctxt ^ " => (" ^ get_term match ctxt ^ ") = (" ^ get_term target ctxt ^ "))\n" ] 
val write_auto = ["  by auto\n\n"]

fun write_lemma (Rewrite_Rule ((Rule_Type DEFINE_RULE)::(Rule_Name name)::rest )) ctxt =
    let
      val [Par param, Match m, Target t] = rest
    in 
      (write_lemma_header name) :: [write_fixes param ctxt, write_shows m t ctxt, write_auto]
    end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_RULE)::(Rule_Name name)::rest )) ctxt =
    let
      val [Par param, Precondition ass, Match m, Target t] = rest
    in 
      (write_lemma_header name) :: [(write_shows_wth_assump ass m t ctxt), write_auto]
    end |
    write_lemma rwr ctxt = raise WRITE_LEMMA_FROM_DSL_REWRITE ("Could not write rewrite rule to lemma, has wrong form" ) (*^ PARSE_REWRITE.to_str rwr)*)

local
  fun write_lemmas_h [] _ = [] |
      write_lemmas_h (c::cs) ctxt = (write_lemma c ctxt) @ write_lemmas_h cs ctxt
in 
  fun write_lemmas cs theory_name theory_imports ctxt
  = write_file_header theory_name theory_imports @ write_lemmas_h cs ctxt @ [write_file_footer]
end

end;
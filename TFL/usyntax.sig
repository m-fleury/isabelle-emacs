signature USyntax_sig =
sig
  structure Utils : Utils_sig

  type 'a binding

  datatype lambda = VAR   of {Name : string, Ty : typ}
                  | CONST of {Name : string, Ty : typ}
                  | COMB  of {Rator: term, Rand : term}
                  | LAMB  of {Bvar : term, Body : term}

  val alpha : typ
  val mk_preterm : cterm -> term

  (* Types *)
  val type_vars  : typ -> typ list
  val type_varsl : typ list -> typ list
  val mk_vartype : string -> typ
  val is_vartype : typ -> bool
  val -->        : typ * typ -> typ
  val strip_type : typ -> typ list * typ
  val strip_prod_type : typ -> typ list
  val match_type: typ -> typ -> typ binding list

  (* Terms *)
  val free_vars  : term -> term list
  val free_varsl : term list -> term list
  val free_vars_lr : term -> term list
  val all_vars   : term -> term list
  val all_varsl  : term list -> term list
  val variant    : term list -> term -> term
  val type_vars_in_term : term -> typ list
  val dest_term  : term -> lambda
  
  (* Prelogic *)
  val aconv     : term -> term -> bool
  val subst     : term binding list -> term -> term
  val inst      : typ binding list -> term -> term
  val beta_conv : term -> term

  (* Construction routines *)
  val mk_var    :{Name : string, Ty : typ} -> term
  val mk_const  :{Name : string, Ty : typ} -> term
  val mk_comb   :{Rator : term, Rand : term} -> term
  val mk_abs    :{Bvar  : term, Body : term} -> term

  val mk_imp    :{ant : term, conseq :  term} -> term
  val mk_select :{Bvar : term, Body : term} -> term
  val mk_forall :{Bvar : term, Body : term} -> term
  val mk_exists :{Bvar : term, Body : term} -> term
  val mk_conj   :{conj1 : term, conj2 : term} -> term
  val mk_disj   :{disj1 : term, disj2 : term} -> term
  val mk_pabs   :{varstruct : term, body : term} -> term

  (* Destruction routines *)
  val dest_var  : term -> {Name : string, Ty : typ}
  val dest_const: term -> {Name : string, Ty : typ}
  val dest_comb : term -> {Rator : term, Rand : term}
  val dest_abs  : term -> {Bvar : term, Body : term}
  val dest_eq     : term -> {lhs : term, rhs : term}
  val dest_imp    : term -> {ant : term, conseq : term}
  val dest_select : term -> {Bvar : term, Body : term}
  val dest_forall : term -> {Bvar : term, Body : term}
  val dest_exists : term -> {Bvar : term, Body : term}
  val dest_neg    : term -> term
  val dest_conj   : term -> {conj1 : term, conj2 : term}
  val dest_disj   : term -> {disj1 : term, disj2 : term}
  val dest_pair   : term -> {fst : term, snd : term}
  val dest_pabs   : term -> {varstruct : term, body : term}

  val lhs   : term -> term
  val rhs   : term -> term
  val rator : term -> term
  val rand  : term -> term
  val bvar  : term -> term
  val body  : term -> term
  

  (* Query routines *)
  val is_var  : term -> bool
  val is_const: term -> bool
  val is_comb : term -> bool
  val is_abs  : term -> bool
  val is_eq     : term -> bool
  val is_imp    : term -> bool
  val is_forall : term -> bool 
  val is_exists : term -> bool 
  val is_neg    : term -> bool
  val is_conj   : term -> bool
  val is_disj   : term -> bool
  val is_pair   : term -> bool
  val is_pabs   : term -> bool

  (* Construction of a term from a list of Preterms *)
  val list_mk_abs    : (term list * term) -> term
  val list_mk_imp    : (term list * term) -> term
  val list_mk_forall : (term list * term) -> term
  val list_mk_exists : (term list * term) -> term
  val list_mk_conj   : term list -> term
  val list_mk_disj   : term list -> term

  (* Destructing a term to a list of Preterms *)
  val strip_comb     : term -> (term * term list)
  val strip_abs      : term -> (term list * term)
  val strip_imp      : term -> (term list * term)
  val strip_forall   : term -> (term list * term)
  val strip_exists   : term -> (term list * term)
  val strip_conj     : term -> term list
  val strip_disj     : term -> term list
  val strip_pair     : term -> term list

  (* Miscellaneous *)
  val mk_vstruct : typ -> term list -> term
  val gen_all    : term -> term
  val find_term  : (term -> bool) -> term -> term
  val find_terms : (term -> bool) -> term -> term list
  val dest_relation : term -> term * term * term
  val is_WFR : term -> bool
  val ARB : typ -> term

  (* Prettyprinting *)
  val Term_to_string : cterm -> string
end;

(*  Title:      HOL/Tools/SMT/smtlib.ML
    Author:     Sascha Boehme, TU Muenchen

Parsing and generating SMT-LIB 2.
*)

signature SMTLIB =
sig
  exception PARSE of int * string
  datatype tree = 
    Num of int |
    BVNum of int * int |
    Dec of int * int |
    Str of string |
    Sym of string |
    Key of string |
    S of tree list
  val parse: string list -> tree
  val pretty_tree: tree -> Pretty.T
  val str_of: tree -> string
end;

structure SMTLIB: SMTLIB =
struct

(* data structures *)

exception PARSE of int * string

datatype tree = 
  Num of int |
  BVNum of int * int |
  Dec of int * int |
  Str of string |
  Sym of string |
  Key of string |
  S of tree list

datatype unfinished = None | String of string | Symbol of string


(* utilities *)

fun !!! l text scan =
  let
    fun err (syms, msg) = (raise PARSE (l,
      "SMTLIB term parser: " ^ text ^ " in token starting with: " ^  implode syms ^ 
      (case msg of NONE => "" | SOME m => "\n" ^ m ())));
  in (Scan.error (Scan.!! err scan)) end;
 
fun read_while pred l = 
  !!! l "empty token"
  (Scan.permissive (
    (!!! l "unexpected character" (Scan.one pred)) ::: (Scan.finite Symbol.stopper (Scan.many pred))
  ))

(* The library version does not keep track of the bit-width and cannot be used for
bases bigger than 10. *)
fun read_radix_int' radix cs =
  let
    val zero = Char.ord #"0";
    val lower_a = Char.ord #"a";
    val upper_A = Char.ord #"A";

    val dec_radix =
      if radix < 10 then radix
      else if radix <= 35 then radix - 10
      else raise ERROR ("Base too big, can only parse numbers made up of digits and characters a-z/A-Z")

    val limit = zero + radix;
    val limit_lower_alphabetic = lower_a + dec_radix
    val limit_upper_alphabetic = upper_A + dec_radix

    fun scan ((num,i), []) = ((num,i), [])
      | scan ((num,i), c :: cs) =
          if zero <= ord c andalso ord c < limit then
            scan ((radix * num + (ord c - zero),(i+1)), cs)
          else if lower_a <= ord c andalso ord c < limit_lower_alphabetic then
            scan ((radix * num + (ord c - lower_a + 10),(i+1)), cs)
          else if upper_A <= ord c andalso ord c < limit_upper_alphabetic then
            scan ((radix * num + (ord c - upper_A + 10),(i+1)), cs) 
          else ((num,i), c :: cs);

  in scan ((0,0), cs) end;


(* numerals and decimals *)

fun read_num sign = read_int >> sign >> Num
fun read_dec sign = (read_int >> sign) --| $$ "." -- read_int >> Dec


fun mk_smt_num (n, NONE) = Num n |
  mk_smt_num (n,SOME m) = Dec (n,m)
fun read_num2 sign = ((read_int >> sign)
 -- (Scan.option ($$ "." |-- read_int))) >> mk_smt_num (*Can parse 024.*)
val is_neg = Scan.optional ($$ "-" >> K ~) I


fun scan_num l = !!! l "Could not read numeral" (is_neg :-- (read_num2 ) >> snd)


val x = scan_num 4 (raw_explode "-064.3")
val _ = @{print}("x",x)


fun int_of cs = fst (read_int cs)

fun read_num l cs =
  (case read_while Symbol.is_ascii_digit l cs of
    (cs1, "." :: cs') =>
      let val (cs2, cs'') = read_while Symbol.is_ascii_digit l cs'
      in (Dec (int_of cs1, int_of cs2), cs'') end |
    (cs1, "/" :: cs') =>
       let val (cs2, cs'') = read_while Symbol.is_ascii_digit l cs'
      in (S[Sym "/", (Dec (int_of cs1, 0)),(Dec (int_of cs2,0))], cs'') end |
    (cs1, cs2) => (Num (int_of cs1), cs2))

fun read_int l ("-"::cs) =
  (case read_while Symbol.is_ascii_digit l cs of
    (cs1, "." :: cs') =>
      let val (cs2, cs'') = read_while Symbol.is_ascii_digit l cs'
      in (Dec (~ (int_of cs1), int_of cs2), cs'') end |
    (cs1, "/" :: cs') =>
       let val (cs2, cs'') = read_while Symbol.is_ascii_digit l cs'
      in (S[Sym "/", (Dec ((~ (int_of cs1)), 0)),(Dec (int_of cs2,0))], cs'') end |
    (cs1, cs2) => (Num (~ (int_of cs1)), cs2))


(* binary numbers *)

fun read_bin l = !!! l "Could not parse binary number" (read_radix_int' 2 >> BVNum)

(* hex numbers *)

fun read_hex l = !!! l "Could not parse hex number" (read_radix_int' 16 >> apsnd (curry (op *) 4) >> BVNum)

(* symbols *)

val symbol_chars = raw_explode "~!@$%^&*_+=<>.?/-" 

fun is_sym c =
  Symbol.is_ascii_letter c orelse
  Symbol.is_ascii_digit c orelse
  member (op =) symbol_chars c

fun read_sym f l cs = read_while is_sym l cs |>> f o implode


(* quoted tokens *)

fun read_quoted stop (escape, replacement) cs =
  let

    fun read _ [] = NONE
      | read rs (cs as (c :: cs')) = ((*@{print}("cs",cs);@{print}("is_prefix (op =) stop cs",is_prefix (op =) stop cs);*)
          if is_prefix (op =) stop cs then
            SOME (implode (rev rs), drop (length stop) cs)
          else if not (null escape) andalso is_prefix (op =) escape cs then
            read (replacement :: rs) (drop (length escape) cs)
          else read (c :: rs) cs')
  in read [] cs end

(*TODO: repair this, should be okay test with Z3 Examples and veriT *)
(*fun read_string cs = read_quoted ["\\", "\""] (["\\", "\\"], "\\") cs |> @{print}
*)
fun read_string cs = read_quoted ["\""] (["\\", "\\"], "\\") cs (*|> @{print}*)
fun read_symbol cs = read_quoted ["|"] ([], "") cs


(* core parser *)

(*
fun read l
  = (($$"(" |-- (Scan.repeat (read l --| Scan.many1 (curry (op =) " ") )) --| $$")") >> S) || (*Der letzte braucht kein Leerzeichen!*)
    ($$"#" |-- (($$"x" |-- read_bin l) || ($$"b" |-- read_bin l))) ||
    ($$":" |-- (read_sym Key l))

val y = @{print}("d",read 4 (raw_explode "(sdf"))
*)

fun read _ [] rest tss = (rest, tss)
  | read l ("(" :: cs) None tss = read l cs None ([] :: tss)
  | read l (")" :: cs) None (ts1 :: ts2 :: tss) =
      read l cs None ((S (rev ts1) :: ts2) :: tss)
  | read l ("#" :: "x" :: cs) None (ts :: tss) =
      token read_hex l cs ts tss
  | read l ("#" :: "b" :: cs) None (ts :: tss) =
      token read_bin l cs ts tss
  | read l (":" :: cs) None (ts :: tss) =
      token (read_sym Key) l cs ts tss
  | read l ("\"" :: cs) None (ts :: tss) =
      quoted read_string String Str l "" cs ts tss
  | read l ("|" :: cs) None (ts :: tss) =
      quoted read_symbol Symbol Sym l "" cs ts tss
  | read l ((c as "!") :: cs) None (ts :: tss) =
      token (fn _ => pair (Sym c)) l cs ts tss
  | read l (c :: cs) None (ts :: tss) =
      if Symbol.is_ascii_blank c then read l cs None (ts :: tss)
      else if Symbol.is_digit c then token read_num l (c :: cs) ts tss
      else if c = "-" andalso (if cs |> null then false else cs |> hd |> Symbol.is_digit) then token read_int l (c :: cs) ts tss (*TODO: make more elegant*)
      else token (read_sym Sym) l (c :: cs) ts tss
  | read l cs (String s) (ts :: tss) =
      quoted read_string String Str l s cs ts tss
  | read l cs (Symbol s) (ts :: tss) =
      quoted read_symbol Symbol Sym l s cs ts tss
  | read l _ _ [] = raise PARSE (l, "bad parser state")

and token f l cs ts tss =
  let val (t, cs') = f l cs
      (*val _ = @{print}("t",t)*)
  in read l cs' None ((t :: ts) :: tss) end

and quoted r f g l s cs ts tss =
  (case r cs of
    NONE => (f (s ^ implode cs), ts :: tss)
  | SOME (s', cs') => ((*@{print}("g (s ^ s') ",g (s ^ s') ); *)read l cs' None ((g (s ^ s') :: ts) :: tss)))
  


(* overall parser *)

fun read_line l line = read l (raw_explode line)

fun add_line line (l, (None, tss)) =
      if size line = 0 orelse nth_string line 0 = ";" then (l + 1, (None, tss))
      else (l + 1, read_line l line None tss)
  | add_line line (l, (unfinished, tss)) =
      (l + 1, read_line l line unfinished tss)

fun finish (_, (None, [[t]])) = t
  | finish (l, _) = raise PARSE (l, "bad nesting")

fun parse lines = finish (fold add_line lines (1, (None, [[]])))


(* pretty printer *)

fun pretty_tree (Num i) = Pretty.str (string_of_int i)
  | pretty_tree (BVNum (i, base)) = Pretty.str (string_of_int i ^ " :: " ^ string_of_int base ^ " word")
  | pretty_tree (Dec (i, j)) =
      Pretty.str (string_of_int i ^ "." ^ string_of_int j)
  | pretty_tree (Str s) =
      raw_explode s
      |> maps (fn "\"" => ["\\", "\""] | "\\" => ["\\", "\\"] | c => [c])
      |> implode
      |> enclose "\"" "\""
      |> Pretty.str
  | pretty_tree (Sym s) =
      if String.isPrefix "(" s (* for bit vector functions *) orelse
         forall is_sym (raw_explode s) then
        Pretty.str s
      else
        Pretty.str ("|" ^ s ^ "|")
  | pretty_tree (Key s) = Pretty.str (":" ^ s)
  | pretty_tree (S trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_tree trees))

val str_of = Pretty.unformatted_string_of o pretty_tree

end;

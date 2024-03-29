(*  Title:      Pure/ML/ml_env.ML
    Author:     Makarius

Toplevel environment for Standard ML and Isabelle/ML within the
implicit context.
*)

signature ML_ENV =
sig
  val Isabelle: string
  val SML: string
  val ML_environment: string Config.T
  val ML_read_global: bool Config.T
  val ML_write_global: bool Config.T
  val inherit: Context.generic list -> Context.generic -> Context.generic
  type operations =
   {read_source: Input.source -> ML_Lex.token Antiquote.antiquote list,
    explode_token: ML_Lex.token -> char list,
    ML_system: bool}
  type environment = {read: string, write: string}
  val parse_environment: Context.generic option -> string -> environment
  val print_environment: environment -> string
  val SML_export: string
  val SML_import: string
  val setup: string -> operations -> theory -> theory
  val Isabelle_operations: operations
  val SML_operations: operations
  val operations: Context.generic option -> string -> operations
  val touch: Context.generic -> Context.generic
  val forget_structure: string -> Context.generic -> Context.generic
  val bootstrap_name_space: Context.generic -> Context.generic
  val add_name_space: string -> ML_Name_Space.T -> Context.generic -> Context.generic
  val make_name_space: string -> ML_Name_Space.T
  val context: ML_Compiler0.context
  val name_space: ML_Name_Space.T
  val check_functor: string -> unit
  val get_breakpoint: Context.generic -> serial -> (bool Unsynchronized.ref * Position.T) option
  val add_breakpoints: (serial * (bool Unsynchronized.ref * Thread_Position.T)) list -> unit
end

structure ML_Env: ML_ENV =
struct

(* named environments *)

val Isabelle = "Isabelle";
val SML = "SML";

val ML_environment = Config.declare_string ("ML_environment", \<^here>) (K Isabelle);


(* global read/write *)

val ML_read_global = Config.declare_bool ("ML_read_global", \<^here>) (K true);
val ML_write_global = Config.declare_bool ("ML_write_global", \<^here>) (K true);

val read_global = Config.apply_generic ML_read_global;
val write_global = Config.apply_generic ML_write_global;


(* name space tables *)

type tables =
  PolyML.NameSpace.Values.value Symtab.table *
  PolyML.NameSpace.TypeConstrs.typeConstr Symtab.table *
  PolyML.NameSpace.Infixes.fixity Symtab.table *
  PolyML.NameSpace.Structures.structureVal Symtab.table *
  PolyML.NameSpace.Signatures.signatureVal Symtab.table *
  PolyML.NameSpace.Functors.functorVal Symtab.table;

val empty_tables: tables =
  (Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty, Symtab.empty);

fun merge_tables
  ((val1, type1, fixity1, structure1, signature1, functor1),
   (val2, type2, fixity2, structure2, signature2, functor2)) : tables =
  (Symtab.merge (K true) (val1, val2),
   Symtab.merge (K true) (type1, type2),
   Symtab.merge (K true) (fixity1, fixity2),
   Symtab.merge (K true) (structure1, structure2),
   Symtab.merge (K true) (signature1, signature2),
   Symtab.merge (K true) (functor1, functor2));

fun update_tables_values vals (val1, type1, fixity1, structure1, signature1, functor1) : tables =
  (fold Symtab.update vals val1, type1, fixity1, structure1, signature1, functor1);

val sml_tables: tables =
  (Symtab.make ML_Name_Space.sml_val,
   Symtab.make ML_Name_Space.sml_type,
   Symtab.make ML_Name_Space.sml_fixity,
   Symtab.make ML_Name_Space.sml_structure,
   Symtab.make ML_Name_Space.sml_signature,
   Symtab.make ML_Name_Space.sml_functor);


(* context data *)

type operations =
 {read_source: Input.source -> ML_Lex.token Antiquote.antiquote list,
  explode_token: ML_Lex.token -> char list,
  ML_system: bool};

local

type env = tables * operations;
type data = env Name_Space.table * (bool Unsynchronized.ref * Position.T) Inttab.table;

val empty_data: data = (Name_Space.empty_table "ML_environment", Inttab.empty);

fun merge_data ((envs1, breakpoints1), (envs2, breakpoints2)) : data =
  ((envs1, envs2) |> Name_Space.join_tables
    (K (fn ((tables1, ops), (tables2, _)) => (merge_tables (tables1, tables2), ops))),
   Inttab.merge (K true) (breakpoints1, breakpoints2));

in

structure Data = Generic_Data
(
  type T = data;
  val empty = empty_data;
  val merge = merge_data;
);

fun inherit contexts = Data.put (Library.foldl1 merge_data (map Data.get contexts));

end;

val get_env = Name_Space.get o #1 o Data.get;
val get_tables = #1 oo get_env;

val touch = Data.map I;

fun update_tables env_name f context = context |> (Data.map o apfst) (fn envs =>
  let val _ = Name_Space.get envs env_name;
  in Name_Space.map_table_entry env_name (apfst f) envs end);

fun forget_structure name context =
  (if write_global context then ML_Name_Space.forget_structure name else ();
    context |> update_tables Isabelle (fn tables =>
      (#1 tables, #2 tables, #3 tables, Symtab.delete_safe name (#4 tables), #5 tables, #6 tables)));


(* environment name *)

type environment = {read: string, write: string};

val separator = ">";

fun parse_environment opt_context environment =
  let
    fun check name =
      (case opt_context of
        NONE =>
          if name = Isabelle then name
          else error ("Bad ML environment name " ^ quote name ^ " -- no context")
      | SOME context => if name = Isabelle then name else (get_env context name; name));

    val spec =
      if environment = "" then
        (case opt_context of
          NONE => Isabelle
        | SOME context => Config.get_generic context ML_environment)
      else environment;
    val (read, write) =
      (case space_explode separator spec of
        [a] => (a, a)
      | [a, b] => (a, b)
      | _ => error ("Malformed ML environment specification: " ^ quote spec));
  in {read = check read, write = check write} end;

fun print_environment {read, write} = read ^ separator ^ write;

val SML_export = print_environment {read = SML, write = Isabelle};
val SML_import = print_environment {read = Isabelle, write = SML};


(* setup operations *)

val ML_system_values =
  #allVal (ML_Name_Space.global) ()
  |> filter (member (op =) ["ML_system_pretty", "ML_system_pp", "ML_system_overload"] o #1);

fun setup env_name ops thy =
  thy |> (Context.theory_map o Data.map o apfst) (fn envs =>
    let
      val thy' = Sign.map_naming (K Name_Space.global_naming) thy;
      val tables =
        (if env_name = Isabelle then empty_tables else sml_tables)
        |> #ML_system ops ? update_tables_values ML_system_values;
      val (_, envs') =
        Name_Space.define (Context.Theory thy') true (Binding.name env_name, (tables, ops)) envs;
    in envs' end);

val Isabelle_operations: operations =
 {read_source = ML_Lex.read_source,
  explode_token = ML_Lex.check_content_of #> Symbol.explode #> maps (Symbol.esc #> String.explode),
  ML_system = false};

val SML_operations: operations =
 {read_source = ML_Lex.read_source_sml,
  explode_token = ML_Lex.check_content_of #> String.explode,
  ML_system = false};

val _ = Theory.setup (setup Isabelle Isabelle_operations #> setup SML SML_operations);

fun operations opt_context environment =
  let val env = #read (parse_environment opt_context environment) in
    (case opt_context of
      NONE => Isabelle_operations
    | SOME context => #2 (get_env context env))
  end;


(* name space *)

val bootstrap_name_space =
  update_tables Isabelle (fn (tables: tables) =>
    let
      fun update entries (x, y) = member (op =) entries x ? Symtab.update (x, y);
      val bootstrap_val = update ML_Name_Space.bootstrap_values;
      val bootstrap_structure = update ML_Name_Space.bootstrap_structures;
      val bootstrap_signature = update ML_Name_Space.bootstrap_signatures;

      val (val1, type1, fixity1, structure1, signature1, functor1) = sml_tables;
      val val2 = val1
        |> fold bootstrap_val (#allVal ML_Name_Space.global ())
        |> Symtab.fold bootstrap_val (#1 tables);
      val structure2 = structure1
        |> fold bootstrap_structure (#allStruct ML_Name_Space.global ())
        |> Symtab.fold bootstrap_structure (#4 tables);
      val signature2 = signature1
        |> fold bootstrap_signature (#allSig ML_Name_Space.global ())
        |> Symtab.fold bootstrap_signature (#5 tables);
    in (val2, type1, fixity1, structure2, signature2, functor1) end);

fun add_name_space env (space: ML_Name_Space.T) =
  update_tables env (fn (val1, type1, fixity1, structure1, signature1, functor1) =>
    let
      val val2 = fold Symtab.update (#allVal space ()) val1;
      val type2 = fold Symtab.update (#allType space ()) type1;
      val fixity2 = fold Symtab.update (#allFix space ()) fixity1;
      val structure2 = fold Symtab.update (#allStruct space ()) structure1;
      val signature2 = fold Symtab.update (#allSig space ()) signature1;
      val functor2 = fold Symtab.update (#allFunct space ()) functor1;
    in (val2, type2, fixity2, structure2, signature2, functor2) end);

fun make_name_space environment : ML_Name_Space.T =
  let
    val {read, write} = parse_environment (Context.get_generic_context ()) environment;

    fun lookup_env sel1 context name = Symtab.lookup (sel1 (get_tables context read)) name;
    fun dest_env sel1 context = Symtab.dest (sel1 (get_tables context read));
    fun enter_env ap1 entry = update_tables write (ap1 (Symtab.update entry));

    fun lookup sel1 sel2 name =
      if read = Isabelle then
        (case Context.get_generic_context () of
          NONE => sel2 ML_Name_Space.global name
        | SOME context =>
            (case lookup_env sel1 context name of
              NONE => if read_global context then sel2 ML_Name_Space.global name else NONE
            | some => some))
      else lookup_env sel1 (Context.the_generic_context ()) name;

    fun all sel1 sel2 () =
      sort_distinct (string_ord o apply2 #1)
        (if read = Isabelle then
          (case Context.get_generic_context () of
            NONE => sel2 ML_Name_Space.global ()
          | SOME context =>
              dest_env sel1 context @
              (if read_global context then sel2 ML_Name_Space.global () else []))
         else dest_env sel1 (Context.the_generic_context ()));

    fun enter ap1 sel2 entry =
      if write = Isabelle then
        (case Context.get_generic_context () of
          NONE => sel2 ML_Name_Space.global entry
        | SOME context =>
            (if write_global context then sel2 ML_Name_Space.global entry else ();
             Context.>> (enter_env ap1 entry)))
      else Context.>> (enter_env ap1 entry);
  in
   {lookupVal    = lookup #1 #lookupVal,
    lookupType   = lookup #2 #lookupType,
    lookupFix    = lookup #3 #lookupFix,
    lookupStruct = lookup #4 #lookupStruct,
    lookupSig    = lookup #5 #lookupSig,
    lookupFunct  = lookup #6 #lookupFunct,
    enterVal     = enter (fn h => fn (a, b, c, d, e, f) => (h a, b, c, d, e, f)) #enterVal,
    enterType    = enter (fn h => fn (a, b, c, d, e, f) => (a, h b, c, d, e, f)) #enterType,
    enterFix     = enter (fn h => fn (a, b, c, d, e, f) => (a, b, h c, d, e, f)) #enterFix,
    enterStruct  = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, h d, e, f)) #enterStruct,
    enterSig     = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, d, h e, f)) #enterSig,
    enterFunct   = enter (fn h => fn (a, b, c, d, e, f) => (a, b, c, d, e, h f)) #enterFunct,
    allVal       = all #1 #allVal,
    allType      = all #2 #allType,
    allFix       = all #3 #allFix,
    allStruct    = all #4 #allStruct,
    allSig       = all #5 #allSig,
    allFunct     = all #6 #allFunct}
  end;

val context: ML_Compiler0.context =
 {name_space = make_name_space "",
  print_depth = NONE,
  here = Position.here oo Position.line_file,
  print = writeln,
  error = error};

val name_space = #name_space context;

val is_functor = is_some o #lookupFunct name_space;

fun check_functor name =
  if not (is_functor "Table") (*mask dummy version of name_space*) orelse is_functor name then ()
  else error ("Unknown ML functor: " ^ quote name);


(* breakpoints *)

val get_breakpoint = Inttab.lookup o #2 o Data.get;

fun add_breakpoints more_breakpoints =
  if is_some (Context.get_generic_context ()) then
    Context.>>
      ((Data.map o apsnd)
        (fold (Inttab.update_new o (apsnd o apsnd) Position.make) more_breakpoints))
  else ();

end;

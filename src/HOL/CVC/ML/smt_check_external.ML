signature SMT_CHECK_EXTERNAL =
sig
  val replay_only: string -> Proof.context -> string list -> string list -> string option -> thm
  val check_smt: string -> string -> string -> string option -> local_theory -> local_theory
  val check_all_benchmarks : string -> string -> string option -> local_theory -> unit
end

structure SMT_Check_External : SMT_CHECK_EXTERNAL =
struct

open SMT_Config
fun debug_msg ctxt = alethe_debug_msg ctxt "smt_check_external"

fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of

fun replay_only solver ctxt problem proof opt_output_file =
let
  val _ = debug_msg ctxt high (fn () => \<^print> ("In replay only function"))

  (*Set solver (for replay but not for invoking)*)
  val ctxt =
    ctxt
    |> I (*TODO: why this?*)
    |> Context.Proof
    |> SMT_Config.select_solver solver
    |> Context.proof_of
    |> Config.put SMT_Config.oracle false (*TODO: Check with Mathias, should this always be the case for cvc5_proof? Then, it should also be added elsewhere*)
  val (name, {command, smt_options, replay, ...}) = SMT_Solver.name_and_info_of ctxt

  val replay_data = SMT_Parse_Problem.parse problem ctxt
  val {ctxt=context, ...} = replay_data
  val _ = debug_msg ctxt high (fn () => \<^print> ("Parsed problem and obtained context"))

  val start0 = Timing.start ()

  val thm = replay context replay_data proof
  val parsing_time = Time.toNanoseconds (#elapsed (Timing.result start0))

  val _ =
    if Option.isSome opt_output_file
    then
      File_Stream.open_append
      (fn stream => File_Stream.outputs stream [(Value.print_int parsing_time ^ "\n")])
      (Path.explode (Option.valOf opt_output_file))
    else ()

  val _ =  Proof_Context.export context ctxt [thm]
in thm end

fun check_smt2 prover problem_file_name proof_file_name opt_output_file local_thy =
let

  (*Get problem and proof file*)
  val ctxt = Local_Theory.target_of local_thy
    |> Config.put SMT_Config.check_external true
    |> SMT_Config.alethe_set_no_provided_assms true 

  val _ =
    if Option.isSome opt_output_file
    then
      let
        val base_name = problem_file_name |> String.tokens (fn c => c = #"/") |> rev |> hd
      in
        File_Stream.open_append
        (fn stream => File_Stream.outputs stream [base_name ^ ", "])
        (Path.explode (Option.valOf opt_output_file))
      end
    else ()

  val problem_file_path = Path.explode problem_file_name
  val proof_file_path = Path.explode proof_file_name

  val problem_lines = problem_file_path |> Bytes.read |> Bytes.split_lines;
  val proof_lines = proof_file_path |> Bytes.read |> Bytes.split_lines;
  val thm = @{thm TrueE}
  val _ = SMT_Config.statistics_msg ctxt (fn current => "PROBLEMFILENAME: " ^ current) problem_file_name
  fun print_error_code code = SMT_Config.statistics_msg ctxt (fn current => "RESULT_CODE: " ^ current) ("-" ^ Int.toString code)
  val print_error = SMT_Config.statistics_msg ctxt (fn current => "RESULT_MSG: " ^ current)

  val (_,i) = (fn () => (replay_only prover ctxt problem_lines proof_lines opt_output_file,0)) ()
    handle
      (*Error Parsing problem*)
      (SMT_Parse_Problem.SMT_PROBLEM_PARSE(msg))
        => (if String.isPrefix "command not supported: " msg
            then
             (print_error ("Unsupported SMT-LIB command in problem: " ^ msg); print_error_code 5; (thm,1))
            else
             (print_error ("Error parsing SMT-LIB problem: " ^ msg); print_error_code 5; (thm,1)))
    | (*Error during Parsing into AST*)
      (SMTLIB.PARSE(l,err))
        => (print_error ("Error parsing SMTLIB into SMTLIB Tree: " ^ err ^ " in line " ^ Int.toString l); print_error_code 5; (thm,1))
    | (*Errors during Parsing Into term*)
      (SMTLIB_Proof.SMTLIB_PARSE ("unknown SMT type",t))
        => (print_error ("Either theory is not supported or parsing instructions for the type are not included in the parser" ^ SMTLIB.str_of t);
            print_error_code 2; (thm,1))
    | (SMTLIB_Proof.SMTLIB_PARSE ("bad SMT term",t))
        => (print_error ("Either theory is not supported or parsing instructions for the term are not included in the parser" ^ SMTLIB.str_of t);
            print_error_code 3; (thm,1))
    | (SMTLIB_Proof.SMTLIB_PARSE(err,t))
        => (print_error ("Unkown error parsing SMTLIB: " ^ err ^ SMTLIB.str_of t); print_error_code 4; (thm,1))
    | (*Errors during Replay*)
      (SMT_Failure.SMT (SMT_Failure.Replay(rule,ERROR msg)))
        => (print_error ("Error replaying step " ^ rule ^ " is: " ^ msg); print_error_code 6; (thm,1))
    | (SMT_Failure.SMT (SMT_Failure.Replay(rule,INTERRUPT)))
        => (print_error ("Interrupt while replaying step (timeout) " ^ rule); print_error_code 7 ; (thm,1))
    | (SMT_Failure.SMT (SMT_Failure.Replay(rule,exn)))
        => (print_error ("Error replaying step " ^ rule ^ " is: " ^ General.exnMessage exn); print_error_code 1; (thm,1))
    | (*Timeout*)
      (SMT_Failure.SMT (SMT_Failure.Time_Out rule))
        => (print_error ("Timeout while reconstructing rule: " ^ rule); print_error_code 7; (thm,1))
    | (SMT_Failure.SMT err)
        => (print_error ("Unkown SMT error " ^ SMT_Failure.string_of_failure err); print_error_code 5; (thm,1))
    | (Timeout.TIMEOUT _) => (print_error ("Timeout"); print_error_code 7; (thm,1))
    | (TYPE x) => (print_error ("Type Error " ^ (fn (a,_,_) => a) x); print_error_code 1; (thm,1))
    | Size => (print_error ("Size "); print_error_code 1; (thm,1))
    | (ERROR x) => (print_error ("Error " ^ x); print_error_code 1 ; (thm,1))

    val _ = (if i = 0 then (SMT_Config.statistics_msg ctxt (fn current => "RESULT_CODE: " ^ current) "0"; print_error_code 0) else ())


fun rm_quotation s = implode (filter_out (fn c => c = "\"") (raw_explode s))

in (i,local_thy) end
          
fun check_smt prover problem_file_name proof_file_name opt_output_file local_thy =
snd (check_smt2 prover problem_file_name proof_file_name opt_output_file local_thy)


fun check_all_benchmarks prover files_dir opt_output_file local_thy =
let
  val ctxt = Local_Theory.target_of local_thy


  val dir_content = files_dir |> Path.explode |> File.read_dir
  val problems_path = filter (fn filename => String.isSuffix ".smt2" filename) dir_content
  val _ =
    if Option.isSome opt_output_file
    then
      File_Stream.open_output (fn stream => File_Stream.outputs stream []) (Path.explode (Option.valOf opt_output_file))
    else ()


  fun check_all [] i = ((),i) |
    check_all (problem_path::ts) i =
    let
      val _ = SMT_Config.trace_msg ctxt (pretty ("problem" ^problem_path)) []


       val problem_path = files_dir ^ problem_path

       val proof_path = Library.unsuffix ".smt2" problem_path |> Library.suffix ".alethe"

    in
      if Path.explode proof_path |> File.is_file
      then
        let
          val (ret,_) = check_smt2 prover problem_path proof_path opt_output_file local_thy
          val ret = (if ret = 0 then 1 else 0)
        in check_all ts (i + ret) end
      else raise ERROR("Could not find proof for problem:" ^ problem_path)
    end

  val nr_checked_successfully = check_all problems_path 0 |> snd
  val _ = @{print}(Library.string_of_int nr_checked_successfully ^ "/"
    ^ Library.string_of_int (length problems_path) ^ " proofs checked without errors. This means that there were: "
    ^ Library.string_of_int (length problems_path - nr_checked_successfully) ^ " errors!")


  val _ = SMT_Config.verbose_msg ctxt (pretty ("------------------------------------------")) []
  val _ = SMT_Config.verbose_msg ctxt (pretty ("------------------------------------------")) []
  val _ = SMT_Config.verbose_msg ctxt (pretty ("------------------------------------------")) []
  val _ = SMT_Config.verbose_msg ctxt (pretty ("Checked proofs in directory " ^ files_dir)) []
  val _ = SMT_Config.verbose_msg ctxt (pretty ("There are " ^ Library.string_of_int (length problems_path) ^ " proofs to be checked!")) []
  val _ = SMT_Config.verbose_msg ctxt (pretty ("Of those " ^ Library.string_of_int nr_checked_successfully ^ " could be checked successfully!")) []

in
  ()
end

end

signature SMT_CHECK_EXTERNAL =
sig
  val replay_only: string -> Proof.context -> string list -> string list -> string option -> thm
  val check_smt: string -> string -> string -> string option -> local_theory -> local_theory
  val check_all_benchmarks : string -> string -> string option -> local_theory -> unit
end

structure SMT_Check_External : SMT_CHECK_EXTERNAL =
struct

fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of

fun replay_only solver ctxt problem proof opt_output_file =
let
  (*Set solver (for replay but not for invoking)*)
  val ctxt =
    ctxt
    |> I
    |> Context.Proof
    |> SMT_Config.select_solver solver
    |> Context.proof_of

  val (_, {command, smt_options, replay, ...}) = SMT_Solver.name_and_info_of ctxt

  val (replay_data, _) = SMT_Parse_Problem.parse problem ctxt
  val {context, ...} = replay_data

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

fun check_smt prover problem_file_name proof_file_name opt_output_file lthy =
let
  (*Get problem and proof file*)
  val ctxt = Local_Theory.target_of lthy |> Config.put SMT_Config.check_external true
  val _ = @{print}(SMT_Config.alethe_no_provided_assms ctxt)
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

  val _ = replay_only prover ctxt problem_lines proof_lines opt_output_file
in lthy end

(*Temporary for evaluation, similarly to spying*)
fun print_error_to_file ctxt i =
  if Config.get ctxt SMT_Config.rec_evaluation
  then File.append (Path.explode ("$ISABELLE_HOME_USER/"
    ^ (Config.get ctxt SMT_Config.statistics_file))) ("-" ^ Int.toString i ^ "}]},\n")
  else ()

  
fun print_reconstruction_error_to_file ctxt i str =
  if Config.get ctxt SMT_Config.rec_evaluation
  then File.append (Path.explode ("$ISABELLE_HOME_USER/"
    ^ (Config.get ctxt SMT_Config.statistics_file))) ("-" ^ Int.toString i ^
    ", \"failed_rule\": \"" ^ str ^ "\"}]},\n")
  else ()

fun check_all_benchmarks prover files_dir opt_output_file local_thy =
let
  val ctxt = Local_Theory.target_of local_thy

  (*Temporary for evaluation*)
  val _ =
    if Config.get ctxt SMT_Config.rec_evaluation
    then File.write (Path.explode ("$ISABELLE_HOME_USER/" ^ (Config.get ctxt SMT_Config.statistics_file))) ("")
    else ()

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
      val _ =
        if Config.get ctxt SMT_Config.rec_evaluation
        then File.append (Path.explode ("$ISABELLE_HOME_USER/" ^
            (Config.get ctxt SMT_Config.statistics_file))) ("{\"benchmark_name\": \"" ^ problem_path
              ^ "\", \"checking\": [{\"solver_config\": \"" ^ (Config.get ctxt SMT_Config.statistics_file)
              ^ "\", \"checking_time\": ")
        else ()

       val problem_path = files_dir ^ problem_path

       val proof_path = Library.unsuffix ".smt2" problem_path |> Library.suffix ".alethe"


    in
      if Path.explode proof_path |> File.is_file
      then
        let
          val (_,i) = (check_smt prover problem_path proof_path opt_output_file local_thy,i+1)
            handle
            (*Error during Parsing into AST*)
            (SMTLIB.PARSE(l,err))
              => (@{print}("Error parsing SMTLIB into SMTLIB Tree: " ^ err ^ " in line " ^ Int.toString l , problem_path);
                  print_error_to_file ctxt 5; (local_thy,i)) |
            (*Errors during Parsing Into term*)
            (SMTLIB_Proof.SMTLIB_PARSE ("unknown SMT type",t))
              => (@{print}(("Either theory is not supported or parsing instructions for the type" ^
                            " are not included in the parser", t), problem_path);
                  print_error_to_file ctxt 2; (local_thy,i)) |
            (SMTLIB_Proof.SMTLIB_PARSE ("bad SMT term",t))
              => (@{print}(("Either theory is not supported or parsing instructions for the term" ^
                            " are not included in the parser", t), problem_path);
                 print_error_to_file ctxt 3; (local_thy,i)) |
            (SMTLIB_Proof.SMTLIB_PARSE(err,t))
              => (@{print}(("Unkown error parsing SMTLIB: " ^ err, t), problem_path);
                  print_error_to_file ctxt 4; (local_thy,i)) |
            (*Errors during Replay*)
            (SMT_Failure.SMT (SMT_Failure.Replay(rule,ERROR msg)))
              => (@{print}("Error replaying step" ^ rule ^ " is: " ^ msg);
                  print_reconstruction_error_to_file ctxt 6 rule; (local_thy,i)) |
            (SMT_Failure.SMT (SMT_Failure.Replay(rule,INTERRUPT)))
               => (@{print}("Timeout");
                  print_error_to_file ctxt 7; (local_thy,i)) |
            (SMT_Failure.SMT (SMT_Failure.Replay(rule,exn)))
              => (@{print}("Error replaying step" ^ rule ^ " is: " ^ General.exnMessage exn);
                  print_reconstruction_error_to_file ctxt 1 rule; (local_thy,i)) |
            (*Timeout*)
            (SMT_Failure.SMT SMT_Failure.Time_Out)
               => (@{print}("Timeout");
                  print_error_to_file ctxt 7; (local_thy,i)) |
            (SMT_Failure.SMT err)
               => (@{print}("Unkown SMT error " ^ SMT_Failure.string_of_failure err, problem_path);
                  print_error_to_file ctxt 5; (local_thy,i)) |
             exp => (@{print}("Some unkown error occured while checking the proof " ^ problem_path);
                  @{print}("exp",exp);
                  print_error_to_file ctxt 1; (local_thy,i))
        in check_all ts i end
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
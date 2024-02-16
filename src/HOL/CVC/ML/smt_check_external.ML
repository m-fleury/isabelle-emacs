signature SMT_CHECK_EXTERNAL =
sig
  val replay_only: string -> Proof.context -> string list -> string list -> string option -> thm
  val check_smt: string -> string -> string -> string option -> local_theory -> local_theory
  val test_all_benchmarks : string -> string -> string option -> local_theory -> unit
end

structure SMT_Check_External : SMT_CHECK_EXTERNAL =
struct

fun replay_only solver ctxt problem proof opt_output_file =
  let
    (*Set solver (for replay but not for invoking)*)
    val ctxt =
      ctxt
      |> I
      |> Context.Proof
      |> SMT_Config.select_solver solver
      |> Context.proof_of
(*  val name_and_info_of: Proof.context -> string * solver_info*)
    val (_, {command, smt_options, replay, ...}) = SMT_Solver.name_and_info_of ctxt

    val (replay_data, _) = SMT_Parse_Problem.parse problem ctxt
    (*val _ = @{print}("replay_data",replay_data)
    val _ = @{print}("proof",proof)*)

    val {context, ...} = replay_data

    val start0 = Timing.start ()
    val _ = @{print}("here")

    val thm = replay context replay_data proof
    val _ = @{print}("thm",thm)

    val parsing_time = Time.toNanoseconds (#elapsed (Timing.result start0))

    val _ = if Option.isSome opt_output_file 
            then
              File_Stream.open_append (fn stream => File_Stream.outputs stream [(Value.print_int parsing_time ^ "\n")]) (Path.explode (Option.valOf opt_output_file))
            else ()

    val _ =  Proof_Context.export context ctxt [thm]

  in thm end

fun check_smt prover problem_file_name proof_file_name opt_output_file lthy =
 let
  val _ = @{print}("prover",prover)

    (*Get problem and proof file*)
    val ctxt = Local_Theory.target_of lthy
    val _ = if Option.isSome opt_output_file 
            then
              let
                val base_name = problem_file_name |> String.tokens (fn c => c = #"/") |> rev |> hd
              in
                File_Stream.open_append (fn stream => File_Stream.outputs stream [base_name ^ ", "]) (Path.explode (Option.valOf opt_output_file))
              end
            else ()

    val problem_file_path = Path.explode problem_file_name
    val proof_file_path = Path.explode proof_file_name

    val problem_lines = problem_file_path |> Bytes.read |> Bytes.split_lines;
    val proof_lines = proof_file_path |> Bytes.read |> Bytes.split_lines;
    val _ = replay_only prover ctxt problem_lines proof_lines opt_output_file
in lthy end

fun test_all_benchmarks prover files_dir opt_output_file local_thy =
let
  val _ = @{print}("prover",prover)
  val dir_content = files_dir |> Path.explode |> File.read_dir
  val problems_path = filter (fn filename => String.isSuffix ".smt2" filename) dir_content
  val _ = if Option.isSome opt_output_file 
          then
            File_Stream.open_output (fn stream => File_Stream.outputs stream []) (Path.explode (Option.valOf opt_output_file))
          else ()

  fun check_all [] i = ((),i) |
      check_all (problem_path::ts) i =
        let
          val problem_path = files_dir ^ problem_path
          val proof_path = Library.unsuffix ".smt2" problem_path |> Library.suffix ".alethe"
          val _ = if Path.explode proof_path |> File.is_file then ()
                  else (@{print}("Could not find proof for problem: ",problem_path);())(*TODO*)


          val (_,i) = (check_smt prover problem_path proof_path opt_output_file local_thy,i+1)
            handle
            (SMTLIB_Proof.SMTLIB_PARSE ("unknown SMT type",t)) 
              => (@{print}(("Either theory is not supported or parsing instructions for the term are not included in the parser", t),problem_path);(local_thy,i)) |
            (SMTLIB_Proof.SMTLIB_PARSE(err,t))
              => (@{print}(("Error parsing SMTLIB: " ^ err, t),problem_path);(local_thy,i)) |
            (SMTLIB.PARSE(l,err))
              => (@{print}("Error parsing SMTLIB into SMTLIB Tree: " ^ err ^ " in line " ^ Int.toString l ,problem_path);(local_thy,i)) |
            (SMT_Failure.SMT err)
              => (@{print}("Error parsing SMTLIB into SMTLIB Tree: " ^ SMT_Failure.string_of_failure err,problem_path);(local_thy,i)) |
            (*(Fail err)
              => (@{print}("Proof could not be checked! " ^ err,problem_path);(local_thy,i)) | (*TODO: Throw error*)*)
            exp => (@{print}("Some error occured while checking the proof ");
          if Option.isSome opt_output_file 
          then
            File_Stream.open_append (fn stream => File_Stream.outputs stream ["error\n"]) (Path.explode (Option.valOf opt_output_file))
          else ();(local_thy,i)) |
            exp => (error (@{make_string}("Some error occured while checking the proof" ^ General.exnMessage exp,problem_path));(local_thy,i))
        in
         check_all ts i
        end

  val nr_checked_successfully = check_all problems_path 0 |> snd
  fun pretty tag lines = Pretty.string_of (Pretty.big_list tag (map Pretty.str lines))
  val ctxt = Local_Theory.target_of local_thy
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
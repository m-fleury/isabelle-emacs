signature SMT_REGRESS =
sig
  val test_all_benchmarks : string -> string -> local_theory -> unit
  val run_regress : bool
end

structure SMT_Regress : SMT_REGRESS =
struct

fun check_smt prover problem_file_name proof_file_name lthy =
 let
    (*Get problem and proof file*)
    val ctxt = Local_Theory.target_of lthy
    val problem_file_path = Path.explode problem_file_name
    val proof_file_path = Path.explode proof_file_name
    (*val _ = @{print}("problem_file_path",problem_file_path)
    val _ = @{print}("proof_file_path",proof_file_path)*)

    val problem_lines = (Bytes.split_lines (Bytes.read problem_file_path));
    val proof_lines = (Bytes.split_lines (Bytes.read proof_file_path));
    (*TODO: This weird empty line is added at the end. Investigate*)
    val proof_lines = take (length proof_lines - 1) proof_lines
    val problem_lines = take (length problem_lines - 1) problem_lines
    (*Replay proof*)
    val _ = SMT_Solver.replay_only prover ctxt problem_lines proof_lines
in lthy end


fun test_all_benchmarks prover files_dir local_thy = 
let
  val files_dir_path = Path.explode files_dir
  val dir_content = File.read_dir files_dir_path
  val problems_path = filter (fn filename => String.isSuffix ".smt2" filename) dir_content

  fun check_all [] i = ((),i) |
      check_all (problem_path::ts) i =
        let
          val problem_path = files_dir ^ problem_path
          val proof_path = Library.unsuffix ".smt2" problem_path |> Library.suffix ".alethe"
          val _ = if Path.explode proof_path |> File.is_file then ()
                  else (@{print}("Could not find proof for problem: ",problem_path);())
          val (_,i) = (check_smt prover problem_path proof_path local_thy,i+1)
            handle
            (Fail err)
              => (@{print}("Proof could not be checked! " ^ err,problem_path);(local_thy,i)) |
            (SMTLIB_Proof.SMTLIB_PARSE ("unknown SMT type",t)) 
              => (@{print}(("Either theory is not supported or parsing instructions for the term are not included in the parser", t),problem_path);(local_thy,i)) |
            (SMTLIB_Proof.SMTLIB_PARSE(err,t))
              => (@{print}(("Error parsing SMTLIB: " ^ err, t),problem_path);(local_thy,i)) |
            (SMTLIB.PARSE(l,err))
              => (@{print}("Error parsing SMTLIB into SMTLIB Tree: " ^ err ^ " in line " ^ Int.toString l ,problem_path);(local_thy,i)) |
            (SMT_Failure.SMT err)
              => (@{print}("Error parsing SMTLIB into SMTLIB Tree: " ^ SMT_Failure.string_of_failure err,problem_path);(local_thy,i)) |
            exp => (error (@{make_string}("Some error occured while checking the proof",problem_path));(local_thy,i))
     (*How to print exp so I can see what it is?*)
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

val run_regress = true

end
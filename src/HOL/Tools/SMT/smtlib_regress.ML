signature SMT_REGRESS =
sig
  val test_all_benchmarks : local_theory -> unit
  val run_regress : bool
end

structure SMT_Regress : SMT_REGRESS =
struct

(*TODO: I would rather use the command check_smt from SMT.thy but
 I need to export this function with ML_antiquotation first?*)
fun check_smt problem_file_name proof_file_name lthy =
 let
    (*Get problem and proof file*)
    val ctxt = Local_Theory.target_of lthy
    val problem_file_path = Path.explode problem_file_name
    val proof_file_path = Path.explode proof_file_name
    val _ = @{print}("problem_file_path",problem_file_path)
    val _ = @{print}("proof_file_path",proof_file_path)

    val problem_lines = (Bytes.split_lines (Bytes.read problem_file_path));
    val proof_lines = (Bytes.split_lines (Bytes.read proof_file_path));
    (*TODO: This weird empty line is added at the end. Investigate*)
    val proof_lines = take (length proof_lines - 1) proof_lines
    val problem_lines = take (length problem_lines - 1) problem_lines
    (*Replay proof*)
    val _ = SMT_Solver.replay_only ctxt problem_lines proof_lines
in lthy end


fun test_all_benchmarks local_thy = 
let
  val files_dir = "~/Sources/QF_UF/Test1/"
  val files_dir_path = Path.explode files_dir
  val dir_content = File.read_dir files_dir_path
  val _ = @{print}("dir_content",dir_content)
  val problems_path = filter (fn filename => String.isSuffix ".smt2" filename) dir_content
  val _ = @{print}("problems_path",problems_path)

  (*val thy = Context.the_global_context () (*TODO: Input theory as string, or choose local?*)
  val local_thy = Proof_Context.get_global thy "SMT"*)

  fun test [] i = ((),i) |
      test (problem_path::ts) i =
        let
          val problem_path = files_dir ^ problem_path
          val proof_path = Library.unsuffix ".smt2" problem_path |> Library.suffix ".smt2.alethe"
          val _ = if Path.explode proof_path |> File.is_file then (@{print}("Found proof for problem",problem_path);())
                  else (@{print}("Add proof for problem",problem_path);())
          val (_,i) = (check_smt problem_path proof_path local_thy,i+1)
                  handle exp => (@{print}("Proof could not be checked!",problem_path);(local_thy,i))
        in
         test ts i
        end

  val nr_checked_successfully = test problems_path 0 |> snd
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
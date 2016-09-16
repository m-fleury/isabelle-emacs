object profile extends isabelle.CI_Profile
{

  import isabelle._

  def threads = 8
  def jobs = 1
  def include = Nil
  def select = List(Path.explode("$ISABELLE_HOME/src/Benchmarks"))

  def pre_hook(args: List[String]) = {}
  def post_hook(results: Build.Results) = {}

  def select_sessions(tree: Sessions.Tree): (List[String], Sessions.Tree) =
    tree.selection(session_groups = List("timing"))

}

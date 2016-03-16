/*  Title:      Pure/Thy/sessions.scala
    Author:     Makarius

Session information.
*/

package isabelle


import scala.collection.SortedSet
import scala.collection.mutable


object Sessions
{
  /* info */

  val ROOT = Path.explode("ROOT")
  val ROOTS = Path.explode("ROOTS")

  def is_pure(name: String): Boolean = name == "Pure"

  sealed case class Info(
    chapter: String,
    select: Boolean,
    pos: Position.T,
    groups: List[String],
    dir: Path,
    parent: Option[String],
    description: String,
    options: Options,
    theories: List[(Boolean, Options, List[Path])],
    files: List[Path],
    document_files: List[(Path, Path)],
    meta_digest: SHA1.Digest)
  {
    def timeout: Time = Time.seconds(options.real("timeout") * options.real("timeout_scale"))
  }


  /* session tree */

  object Tree
  {
    def apply(infos: Seq[(String, Info)]): Tree =
    {
      val graph1 =
        (Graph.string[Info] /: infos) {
          case (graph, (name, info)) =>
            if (graph.defined(name))
              error("Duplicate session " + quote(name) + Position.here(info.pos) +
                Position.here(graph.get_node(name).pos))
            else graph.new_node(name, info)
        }
      val graph2 =
        (graph1 /: graph1.iterator) {
          case (graph, (name, (info, _))) =>
            info.parent match {
              case None => graph
              case Some(parent) =>
                if (!graph.defined(parent))
                  error("Bad parent session " + quote(parent) + " for " +
                    quote(name) + Position.here(info.pos))

                try { graph.add_edge_acyclic(parent, name) }
                catch {
                  case exn: Graph.Cycles[_] =>
                    error(cat_lines(exn.cycles.map(cycle =>
                      "Cyclic session dependency of " +
                        cycle.map(c => quote(c.toString)).mkString(" via "))) +
                          Position.here(info.pos))
                }
            }
        }
      new Tree(graph2)
    }
  }

  final class Tree private(val graph: Graph[String, Info])
    extends PartialFunction[String, Info]
  {
    def apply(name: String): Info = graph.get_node(name)
    def isDefinedAt(name: String): Boolean = graph.defined(name)

    def selection(
      requirements: Boolean = false,
      all_sessions: Boolean = false,
      exclude_session_groups: List[String] = Nil,
      exclude_sessions: List[String] = Nil,
      session_groups: List[String] = Nil,
      sessions: List[String] = Nil): (List[String], Tree) =
    {
      val bad_sessions =
        SortedSet((exclude_sessions ::: sessions).filterNot(isDefinedAt(_)): _*).toList
      if (bad_sessions.nonEmpty) error("Undefined session(s): " + commas_quote(bad_sessions))

      val excluded =
      {
        val exclude_group = exclude_session_groups.toSet
        val exclude_group_sessions =
          (for {
            (name, (info, _)) <- graph.iterator
            if apply(name).groups.exists(exclude_group)
          } yield name).toList
        graph.all_succs(exclude_group_sessions ::: exclude_sessions).toSet
      }

      val pre_selected =
      {
        if (all_sessions) graph.keys
        else {
          val select_group = session_groups.toSet
          val select = sessions.toSet
          (for {
            (name, (info, _)) <- graph.iterator
            if info.select || select(name) || apply(name).groups.exists(select_group)
          } yield name).toList
        }
      }.filterNot(excluded)

      val selected =
        if (requirements) (graph.all_preds(pre_selected).toSet -- pre_selected).toList
        else pre_selected

      val graph1 = graph.restrict(graph.all_preds(selected).toSet)
      (selected, new Tree(graph1))
    }

    def ancestors(name: String): List[String] =
      graph.all_preds(List(name)).tail.reverse

    def topological_order: List[(String, Info)] =
      graph.topological_order.map(name => (name, apply(name)))

    override def toString: String = graph.keys_iterator.mkString("Sessions.Tree(", ", ", ")")
  }


  /* parser */

  private val CHAPTER = "chapter"
  private val SESSION = "session"
  private val IN = "in"
  private val DESCRIPTION = "description"
  private val OPTIONS = "options"
  private val GLOBAL_THEORIES = "global_theories"
  private val THEORIES = "theories"
  private val FILES = "files"
  private val DOCUMENT_FILES = "document_files"

  lazy val root_syntax =
    Outer_Syntax.init() + "(" + ")" + "+" + "," + "=" + "[" + "]" +
      (CHAPTER, Keyword.THY_DECL) + (SESSION, Keyword.THY_DECL) +
      IN + DESCRIPTION + OPTIONS + GLOBAL_THEORIES + THEORIES + FILES + DOCUMENT_FILES

  object Parser extends Parse.Parser
  {
    private abstract class Entry
    private sealed case class Chapter(name: String) extends Entry
    private sealed case class Session_Entry(
      pos: Position.T,
      name: String,
      groups: List[String],
      path: String,
      parent: Option[String],
      description: String,
      options: List[Options.Spec],
      theories: List[(Boolean, List[Options.Spec], List[String])],
      files: List[String],
      document_files: List[(String, String)]) extends Entry

    private val chapter: Parser[Chapter] =
    {
      val chapter_name = atom("chapter name", _.is_name)

      command(CHAPTER) ~! chapter_name ^^ { case _ ~ a => Chapter(a) }
    }

    private val session_entry: Parser[Session_Entry] =
    {
      val session_name = atom("session name", _.is_name)

      val option =
        name ~ opt($$$("=") ~! name ^^ { case _ ~ x => x }) ^^ { case x ~ y => (x, y) }
      val options = $$$("[") ~> rep1sep(option, $$$(",")) <~ $$$("]")

      val theories =
        ($$$(GLOBAL_THEORIES) | $$$(THEORIES)) ~!
          ((options | success(Nil)) ~ rep(theory_xname)) ^^
          { case x ~ (y ~ z) => (x == GLOBAL_THEORIES, y, z) }

      val document_files =
        $$$(DOCUMENT_FILES) ~!
          (($$$("(") ~! ($$$(IN) ~! (path ~ $$$(")"))) ^^
              { case _ ~ (_ ~ (x ~ _)) => x } | success("document")) ~
            rep1(path)) ^^ { case _ ~ (x ~ y) => y.map((x, _)) }

      command(SESSION) ~!
        (position(session_name) ~
          (($$$("(") ~! (rep1(name) <~ $$$(")")) ^^ { case _ ~ x => x }) | success(Nil)) ~
          (($$$(IN) ~! path ^^ { case _ ~ x => x }) | success(".")) ~
          ($$$("=") ~!
            (opt(session_name ~! $$$("+") ^^ { case x ~ _ => x }) ~
              (($$$(DESCRIPTION) ~! text ^^ { case _ ~ x => x }) | success("")) ~
              (($$$(OPTIONS) ~! options ^^ { case _ ~ x => x }) | success(Nil)) ~
              rep1(theories) ~
              (($$$(FILES) ~! rep1(path) ^^ { case _ ~ x => x }) | success(Nil)) ~
              (rep(document_files) ^^ (x => x.flatten))))) ^^
        { case _ ~ ((a, pos) ~ b ~ c ~ (_ ~ (d ~ e ~ f ~ g ~ h ~ i))) =>
            Session_Entry(pos, a, b, c, d, e, f, g, h, i) }
    }

    def parse(options: Options, select: Boolean, dir: Path): List[(String, Info)] =
    {
      def make_info(entry_chapter: String, entry: Session_Entry): (String, Info) =
      {
        try {
          val name = entry.name

          if (name == "") error("Bad session name")
          if (is_pure(name) && entry.parent.isDefined) error("Illegal parent session")
          if (!is_pure(name) && !entry.parent.isDefined) error("Missing parent session")

          val session_options = options ++ entry.options

          val theories =
            entry.theories.map({ case (global, opts, thys) =>
              (global, session_options ++ opts, thys.map(Path.explode(_))) })
          val files = entry.files.map(Path.explode(_))
          val document_files =
            entry.document_files.map({ case (s1, s2) => (Path.explode(s1), Path.explode(s2)) })

          val meta_digest =
            SHA1.digest((entry_chapter, name, entry.parent, entry.options,
              entry.theories, entry.files, entry.document_files).toString)

          val info =
            Info(entry_chapter, select, entry.pos, entry.groups, dir + Path.explode(entry.path),
              entry.parent, entry.description, session_options, theories, files,
              document_files, meta_digest)

          (name, info)
        }
        catch {
          case ERROR(msg) =>
            error(msg + "\nThe error(s) above occurred in session entry " +
              quote(entry.name) + Position.here(entry.pos))
        }
      }

      val root = dir + ROOT
      if (root.is_file) {
        val toks = Token.explode(root_syntax.keywords, File.read(root))
        val start = Token.Pos.file(root.implode)

        parse_all(rep(chapter | session_entry), Token.reader(toks, start)) match {
          case Success(result, _) =>
            var entry_chapter = "Unsorted"
            val infos = new mutable.ListBuffer[(String, Info)]
            result.foreach {
              case Chapter(name) => entry_chapter = name
              case entry: Session_Entry => infos += make_info(entry_chapter, entry)
            }
            infos.toList
          case bad => error(bad.toString)
        }
      }
      else Nil
    }
  }


  /* load sessions from certain directories */

  private def is_session_dir(dir: Path): Boolean =
    (dir + ROOT).is_file || (dir + ROOTS).is_file

  private def check_session_dir(dir: Path): Path =
    if (is_session_dir(dir)) dir
    else error("Bad session root directory: " + dir.toString)

  def load(options: Options, dirs: List[Path] = Nil, select_dirs: List[Path] = Nil): Tree =
  {
    def load_dir(select: Boolean, dir: Path): List[(String, Info)] =
      load_root(select, dir) ::: load_roots(select, dir)

    def load_root(select: Boolean, dir: Path): List[(String, Info)] =
      Parser.parse(options, select, dir)

    def load_roots(select: Boolean, dir: Path): List[(String, Info)] =
    {
      val roots = dir + ROOTS
      if (roots.is_file) {
        for {
          line <- split_lines(File.read(roots))
          if !(line == "" || line.startsWith("#"))
          dir1 =
            try { check_session_dir(dir + Path.explode(line)) }
            catch {
              case ERROR(msg) =>
                error(msg + "\nThe error(s) above occurred in session catalog " + roots.toString)
            }
          info <- load_dir(select, dir1)
        } yield info
      }
      else Nil
    }

    val default_dirs = Isabelle_System.components().filter(is_session_dir(_))
    dirs.foreach(check_session_dir(_))
    select_dirs.foreach(check_session_dir(_))

    Tree(
      for {
        (select, dir) <- (default_dirs ::: dirs).map((false, _)) ::: select_dirs.map((true, _))
        info <- load_dir(select, dir)
      } yield info)
  }


  /* persistent store */

  def log(name: String): Path = Path.basic("log") + Path.basic(name)
  def log_gz(name: String): Path = log(name).ext("gz")

  def store(system_mode: Boolean = false): Store = new Store(system_mode)

  class Store private [Sessions](system_mode: Boolean)
  {
    val output_dir: Path =
      if (system_mode) Path.explode("~~/heaps/$ML_IDENTIFIER")
      else Path.explode("$ISABELLE_OUTPUT")

    val browser_info: Path =
      if (system_mode) Path.explode("~~/browser_info")
      else Path.explode("$ISABELLE_BROWSER_INFO")

    val input_dirs =
      if (system_mode) List(output_dir)
      else {
        val ml_ident = Path.explode("$ML_IDENTIFIER").expand
        output_dir :: Path.split(Isabelle_System.getenv_strict("ISABELLE_PATH")).map(_ + ml_ident)
      }

    //optional heap + log_gz
    def find(name: String): Option[(Path, Path)] =
      input_dirs.find(dir => (dir + log_gz(name)).is_file).map(dir =>
        (dir + Path.basic(name), dir + log_gz(name)))

    def find_heap(name: String): Option[Path] =
      input_dirs.map(_ + Path.basic(name)).find(_.is_file)

    def find_log(name: String): Option[Path] =
      input_dirs.map(_ + log(name)).find(_.is_file)

    def find_log_gz(name: String): Option[Path] =
      input_dirs.map(_ + log_gz(name)).find(_.is_file)

    def prepare_output() { Isabelle_System.mkdirs(output_dir + Path.basic("log")) }
  }
}

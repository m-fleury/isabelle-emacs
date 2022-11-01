/*  Title:      Pure/Tools/sync.scala
    Author:     Makarius

Synchronize Isabelle + AFP repositories.
*/

package isabelle


object Sync {
  /* session images */

  def find_images(options: Options, session_images: List[String],
    dirs: List[Path] = Nil
  ): List[String] = {
    if (session_images.isEmpty) Nil
    else {
      val store = Sessions.store(options)
      val sessions_structure = Sessions.load_structure(options, dirs = dirs)
      sessions_structure.build_requirements(session_images).flatMap { session =>
        val heap =
          store.find_heap(session).map(_.expand).map(path =>
            File.standard_path(path.dir.dir) + "/./" + path.dir.file_name + "/" + path.file_name)
        val db =
          store.find_database(session).map(_.expand).map(path =>
            File.standard_path(path.dir.dir.dir) + "/./" + path.dir.dir.file_name + "/" +
              path.dir.file_name + "/" + path.file_name)
        heap.toList ::: db.toList
      }
    }
  }


  /* sync */

  def sync(options: Options, context: Rsync.Context, target: String,
    verbose: Boolean = false,
    thorough: Boolean = false,
    purge_heaps: Boolean = false,
    session_images: List[String] = Nil,
    preserve_jars: Boolean = false,
    dry_run: Boolean = false,
    rev: String = "",
    afp_root: Option[Path] = None,
    afp_rev: String = ""
  ): Unit = {
    val hg = Mercurial.self_repository()
    val afp_hg = afp_root.map(Mercurial.repository(_))

    val more_filter = if (preserve_jars) List("include *.jar", "protect *.jar") else Nil

    def sync(hg: Mercurial.Repository, dest: String, r: String,
      contents: List[File.Content] = Nil, filter: List[String] = Nil
    ): Unit = {
      hg.sync(context, dest, rev = r, verbose = verbose, thorough = thorough, dry_run = dry_run,
        contents = contents, filter = filter ::: more_filter)
    }

    context.progress.echo_if(verbose, "\n* Isabelle repository:")
    val filter_heaps = if (purge_heaps) Nil else List("protect /heaps", "protect /heaps/**")
    sync(hg, target, rev,
      contents = List(File.content(Path.explode("etc/ISABELLE_ID"), hg.id(rev = rev))),
      filter = filter_heaps ::: List("protect /AFP"))

    for (hg <- afp_hg) {
      context.progress.echo_if(verbose, "\n* AFP repository:")
      sync(hg, Rsync.append(target, "AFP"), afp_rev)
    }

    val images =
      find_images(options, session_images,
        dirs = afp_root.map(_ + Path.explode("thys")).toList)
    if (images.nonEmpty) {
      context.progress.echo_if(verbose, "\n* Session images:")
      Rsync.exec(context, verbose = verbose, thorough = thorough, dry_run = dry_run,
        args = List("--relative", "--") ::: images ::: List(Rsync.append(target, "heaps/"))).check
    }
  }

  val isabelle_tool =
    Isabelle_Tool("sync", "synchronize Isabelle + AFP repositories",
      Scala_Project.here, { args =>
        var afp_root: Option[Path] = None
        var purge_heaps = false
        var session_images = List.empty[String]
        var preserve_jars = false
        var protect_args = false
        var thorough = false
        var afp_rev = ""
        var dry_run = false
        var ssh_port = 0
        var rev = ""
        var ssh_control_path = ""
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle sync [OPTIONS] TARGET

  Options are:
    -A ROOT      include AFP with given root directory (":" for """ + AFP.BASE.implode + """)
    -H           purge heaps directory on target
    -I NAME      include session heap image and build database
                 (based on accidental local state)
    -J           preserve *.jar files
    -P           protect spaces in target file names: more robust, less portable
    -S PATH      SSH control path for connection multiplexing
    -T           thorough treatment of file content and directory times
    -a REV       explicit AFP revision (default: state of working directory)
    -n           no changes: dry-run
    -p PORT      SSH port
    -r REV       explicit revision (default: state of working directory)
    -v           verbose

  Synchronize Isabelle + AFP repositories, based on "isabelle hg_sync".
""",
          "A:" -> (arg => afp_root = Some(if (arg == ":") AFP.BASE else Path.explode(arg))),
          "H" -> (_ => purge_heaps = true),
          "I:" -> (arg => session_images = session_images ::: List(arg)),
          "J" -> (_ => preserve_jars = true),
          "P" -> (_ => protect_args = true),
          "S:" -> (arg => ssh_control_path = arg),
          "T" -> (_ => thorough = true),
          "a:" -> (arg => afp_rev = arg),
          "n" -> (_ => dry_run = true),
          "p:" -> (arg => ssh_port = Value.Int.parse(arg)),
          "r:" -> (arg => rev = arg),
          "v" -> (_ => verbose = true))

        val more_args = getopts(args)
        val target =
          more_args match {
            case List(target) => target
            case _ => getopts.usage()
          }

        val options = Options.init()
        val progress = new Console_Progress
        val context =
          Rsync.Context(progress, ssh_port = ssh_port, ssh_control_path = ssh_control_path,
            protect_args = protect_args)
        sync(options, context, target, verbose = verbose, thorough = thorough,
          purge_heaps = purge_heaps, session_images = session_images, preserve_jars = preserve_jars,
          dry_run = dry_run, rev = rev, afp_root = afp_root, afp_rev = afp_rev)
      }
    )
}

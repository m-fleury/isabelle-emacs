/*  Title:      Pure/System/components.scala
    Author:     Makarius

Isabelle system components.
*/

package isabelle


import java.io.{File => JFile}


object Components {
  /* archive name */

  object Archive {
    val suffix: String = ".tar.gz"

    def apply(name: String): String =
      if (name == "") error("Bad component name: " + quote(name))
      else name + suffix

    def unapply(archive: String): Option[String] = {
      for {
        name0 <- Library.try_unsuffix(suffix, archive)
        name <- proper_string(name0)
      } yield name
    }

    def get_name(archive: String): String =
      unapply(archive) getOrElse
        error("Bad component archive name (expecting .tar.gz): " + quote(archive))
  }


  /* component collections */

  def default_component_repository: String =
    Isabelle_System.getenv("ISABELLE_COMPONENT_REPOSITORY")

  val default_components_base: Path = Path.explode("$ISABELLE_COMPONENTS_BASE")

  def admin(dir: Path): Path = dir + Path.explode("Admin/components")

  def contrib(dir: Path = Path.current, name: String = ""): Path =
    dir + Path.explode("contrib") + Path.explode(name)

  def unpack(dir: Path, archive: Path, progress: Progress = new Progress): String = {
    val name = Archive.get_name(archive.file_name)
    progress.echo("Unpacking " + name)
    Isabelle_System.gnutar("-xzf " + File.bash_path(archive), dir = dir).check
    name
  }

  def resolve(base_dir: Path, names: List[String],
    target_dir: Option[Path] = None,
    copy_dir: Option[Path] = None,
    progress: Progress = new Progress
  ): Unit = {
    Isabelle_System.make_directory(base_dir)
    for (name <- names) {
      val archive_name = Archive(name)
      val archive = base_dir + Path.explode(archive_name)
      if (!archive.is_file) {
        val remote = Components.default_component_repository + "/" + archive_name
        Isabelle_System.download_file(remote, archive, progress = progress)
      }
      for (dir <- copy_dir) {
        Isabelle_System.make_directory(dir)
        Isabelle_System.copy_file(archive, dir)
      }
      unpack(target_dir getOrElse base_dir, archive, progress = progress)
    }
  }

  private val platforms_family: Map[Platform.Family.Value, Set[String]] =
    Map(
      Platform.Family.linux_arm -> Set("arm64-linux", "arm64_32-linux"),
      Platform.Family.linux -> Set("x86_64-linux", "x86_64_32-linux"),
      Platform.Family.macos ->
        Set("arm64-darwin", "arm64_32-darwin", "x86_64-darwin", "x86_64_32-darwin"),
      Platform.Family.windows ->
        Set("x86_64-cygwin", "x86_64-windows", "x86_64_32-windows", "x86-windows"))

  private val platforms_all: Set[String] =
    Set("x86-linux", "x86-cygwin") ++ platforms_family.iterator.flatMap(_._2)

  def purge(dir: Path, platform: Platform.Family.Value): Unit = {
    val purge_set = platforms_all -- platforms_family(platform)

    File.find_files(dir.file,
      (file: JFile) => file.isDirectory && purge_set(file.getName),
      include_dirs = true).foreach(Isabelle_System.rm_tree)
  }


  /* component directories */

  def directories(): List[Path] =
    Path.split(Isabelle_System.getenv_strict("ISABELLE_COMPONENTS"))


  /* component directory content */

  def settings(dir: Path = Path.current): Path = dir + Path.explode("etc/settings")
  def components(dir: Path = Path.current): Path = dir + Path.explode("etc/components")

  def check_dir(dir: Path): Boolean =
    settings(dir).is_file || components(dir).is_file

  def read_components(dir: Path): List[String] =
    split_lines(File.read(components(dir))).filter(_.nonEmpty)

  def write_components(dir: Path, lines: List[String]): Unit =
    File.write(components(dir), terminate_lines(lines))


  /* component repository content */

  val components_sha1: Path = Path.explode("~~/Admin/components/components.sha1")

  sealed case class SHA1_Digest(digest: SHA1.Digest, name: String) {
    override def toString: String = digest.shasum(name)
  }

  def read_components_sha1(lines: List[String] = Nil): List[SHA1_Digest] =
    (proper_list(lines) getOrElse split_lines(File.read(components_sha1))).flatMap(line =>
      Word.explode(line) match {
        case Nil => None
        case List(sha1, name) => Some(SHA1_Digest(SHA1.fake_digest(sha1), name))
        case _ => error("Bad components.sha1 entry: " + quote(line))
      })

  def write_components_sha1(entries: List[SHA1_Digest]): Unit =
    File.write(components_sha1, entries.sortBy(_.name).mkString("", "\n", "\n"))


  /** manage user components **/

  val components_path: Path = Path.explode("$ISABELLE_HOME_USER/etc/components")

  def read_components(): List[String] =
    if (components_path.is_file) Library.trim_split_lines(File.read(components_path))
    else Nil

  def write_components(lines: List[String]): Unit = {
    Isabelle_System.make_directory(components_path.dir)
    File.write(components_path, Library.terminate_lines(lines))
  }

  def update_components(add: Boolean, path0: Path, progress: Progress = new Progress): Unit = {
    val path = path0.expand.absolute
    if (!check_dir(path) && !Sessions.is_session_dir(path)) error("Bad component directory: " + path)

    val lines1 = read_components()
    val lines2 =
      lines1.filter(line =>
        line.isEmpty || line.startsWith("#") || !File.eq(Path.explode(line), path))
    val lines3 = if (add) lines2 ::: List(path.implode) else lines2

    if (lines1 != lines3) write_components(lines3)

    val prefix = if (lines1 == lines3) "Unchanged" else if (add) "Added" else "Removed"
    progress.echo(prefix + " component " + path)
  }


  /* main entry point */

  def main(args: Array[String]): Unit = {
    Command_Line.tool {
      for (arg <- args) {
        val add =
          if (arg.startsWith("+")) true
          else if (arg.startsWith("-")) false
          else error("Bad argument: " + quote(arg))
        val path = Path.explode(arg.substring(1))
        update_components(add, path, progress = new Console_Progress)
      }
    }
  }


  /** build and publish components **/

  def build_components(
    options: Options,
    components: List[Path],
    progress: Progress = new Progress,
    publish: Boolean = false,
    force: Boolean = false,
    update_components_sha1: Boolean = false
  ): Unit = {
    val archives: List[Path] =
      for (path <- components) yield {
        path.file_name match {
          case Archive(_) => path
          case name =>
            if (!path.is_dir) error("Bad component directory: " + path)
            else if (!check_dir(path)) {
              error("Malformed component directory: " + path +
                "\n  (requires " + settings() + " or " + Components.components() + ")")
            }
            else {
              val component_path = path.expand
              val archive_dir = component_path.dir
              val archive_name = Archive(name)

              val archive = archive_dir + Path.explode(archive_name)
              if (archive.is_file && !force) {
                error("Component archive already exists: " + archive)
              }

              progress.echo("Packaging " + archive_name)
              Isabelle_System.gnutar("-czf " + File.bash_path(archive) + " " + Bash.string(name),
                dir = archive_dir).check

              archive
            }
        }
      }

    if ((publish && archives.nonEmpty) || update_components_sha1) {
      val server = options.string("isabelle_components_server")
      if (server.isEmpty) error("Undefined option isabelle_components_server")

      using(SSH.open_session(options, server)) { ssh =>
        val components_dir = Path.explode(options.string("isabelle_components_dir"))
        val contrib_dir = Path.explode(options.string("isabelle_components_contrib_dir"))

        for (dir <- List(components_dir, contrib_dir) if !ssh.is_dir(dir)) {
          error("Bad remote directory: " + dir)
        }

        if (publish) {
          for (archive <- archives) {
            val archive_name = archive.file_name
            val name = Archive.get_name(archive_name)
            val remote_component = components_dir + archive.base
            val remote_contrib = contrib_dir + Path.explode(name)

            // component archive
            if (ssh.is_file(remote_component) && !force) {
              error("Remote component archive already exists: " + remote_component)
            }
            progress.echo("Uploading " + archive_name)
            ssh.write_file(remote_component, archive)

            // contrib directory
            val is_standard_component =
              Isabelle_System.with_tmp_dir("component") { tmp_dir =>
                Isabelle_System.gnutar("-xzf " + File.bash_path(archive), dir = tmp_dir).check
                check_dir(tmp_dir + Path.explode(name))
              }
            if (is_standard_component) {
              if (ssh.is_dir(remote_contrib)) {
                if (force) ssh.rm_tree(remote_contrib)
                else error("Remote component directory already exists: " + remote_contrib)
              }
              progress.echo("Unpacking remote " + archive_name)
              ssh.execute("tar -C " + ssh.bash_path(contrib_dir) + " -xzf " +
                ssh.bash_path(remote_component)).check
            }
            else {
              progress.echo_warning("No unpacking of non-standard component: " + archive_name)
            }
          }
        }

        // remote SHA1 digests
        if (update_components_sha1) {
          val lines =
            for {
              entry <- ssh.read_dir(components_dir)
              if ssh.is_file(components_dir + Path.basic(entry)) &&
                entry.endsWith(Archive.suffix)
            }
            yield {
              progress.echo("Digesting remote " + entry)
              ssh.execute("cd " + ssh.bash_path(components_dir) +
                "; sha1sum " + Bash.string(entry)).check.out
            }
          write_components_sha1(read_components_sha1(lines))
        }
      }
    }

    // local SHA1 digests
    {
      val new_entries =
        for (archive <- archives)
        yield {
          val name = archive.file_name
          progress.echo("Digesting local " + name)
          SHA1_Digest(SHA1.digest(archive), name)
        }
      val new_names = new_entries.map(_.name).toSet

      write_components_sha1(
        new_entries :::
        read_components_sha1().filterNot(entry => new_names.contains(entry.name)))
    }
  }


  /* Isabelle tool wrapper */

  private val relevant_options =
    List("isabelle_components_server", "isabelle_components_dir", "isabelle_components_contrib_dir")

  val isabelle_tool =
    Isabelle_Tool("build_components", "build and publish Isabelle components",
      Scala_Project.here,
      { args =>
        var publish = false
        var update_components_sha1 = false
        var force = false
        var options = Options.init()

        def show_options: String =
          cat_lines(relevant_options.flatMap(options.get).map(_.print))

        val getopts = Getopts("""
Usage: isabelle build_components [OPTIONS] ARCHIVES... DIRS...

  Options are:
    -P           publish on SSH server (see options below)
    -f           force: overwrite existing component archives and directories
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -u           update all SHA1 keys in Isabelle repository Admin/components

  Build and publish Isabelle components as .tar.gz archives on SSH server,
  depending on system options:

""" + Library.indent_lines(2, show_options) + "\n",
          "P" -> (_ => publish = true),
          "f" -> (_ => force = true),
          "o:" -> (arg => options = options + arg),
          "u" -> (_ => update_components_sha1 = true))

        val more_args = getopts(args)
        if (more_args.isEmpty && !update_components_sha1) getopts.usage()

        val progress = new Console_Progress

        build_components(options, more_args.map(Path.explode), progress = progress,
          publish = publish, force = force, update_components_sha1 = update_components_sha1)
      })
}

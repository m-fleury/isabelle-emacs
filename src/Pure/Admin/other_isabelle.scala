/*  Title:      Pure/Admin/other_isabelle.scala
    Author:     Makarius

Manage other Isabelle distributions: support historic versions starting from
tag "build_history_base".
*/

package isabelle


object Other_Isabelle {
  def apply(
    root: Path,
    isabelle_identifier: String = "",
    ssh: SSH.System = SSH.Local,
    progress: Progress = new Progress
  ): Other_Isabelle = {
    val (isabelle_home, url_prefix) =
      ssh match {
        case session: SSH.Session => (ssh.absolute_path(root), session.rsync_prefix)
        case _ =>
          if (proper_string(System.getenv("ISABELLE_SETTINGS_PRESENT")).isDefined) {
            error("Cannot manage other Isabelle distribution: global ISABELLE_SETTINGS_PRESENT")
          }
          (root.canonical, "")
      }
    val isabelle_home_url = url_prefix + isabelle_home.implode
    new Other_Isabelle(isabelle_home, isabelle_identifier, isabelle_home_url, ssh, progress)
  }
}

final class Other_Isabelle private(
  val isabelle_home: Path,
  val isabelle_identifier: String,
  isabelle_home_url: String,
  ssh: SSH.System,
  progress: Progress
) {
  override def toString: String = isabelle_home_url


  /* static system */

  def bash(
    script: String,
    redirect: Boolean = false,
    echo: Boolean = false,
    strict: Boolean = true
  ): Process_Result = {
    ssh.execute(
      Isabelle_System.export_isabelle_identifier(isabelle_identifier) +
        "cd " + ssh.bash_path(isabelle_home) + "\n" + script,
      progress_stdout = progress.echo_if(echo, _),
      progress_stderr = progress.echo_if(echo, _),
      redirect = redirect,
      settings = false,
      strict = strict)
  }

  def getenv(name: String): String =
    bash("bin/isabelle getenv -b " + Bash.string(name)).check.out

  val settings: Isabelle_System.Settings = (name: String) => getenv(name)

  def expand_path(path: Path): Path = path.expand_env(settings)
  def bash_path(path: Path): String = Bash.string(expand_path(path).implode)

  val isabelle_home_user: Path = expand_path(Path.explode("$ISABELLE_HOME_USER"))

  def etc: Path = isabelle_home_user + Path.explode("etc")
  def etc_settings: Path = etc + Path.explode("settings")
  def etc_preferences: Path = etc + Path.explode("preferences")


  /* components */

  def init_components(
    component_repository: String = Components.default_component_repository,
    components_base: String = Components.standard_components_base,
    catalogs: List[String] = Components.default_catalogs,
    components: List[String] = Nil
  ): List[String] = {
    val admin = Components.admin(Path.ISABELLE_HOME).implode

    ("ISABELLE_COMPONENT_REPOSITORY=" + Bash.string(component_repository)) ::
    catalogs.map(name =>
      "init_components " + quote(components_base) + " " + quote(admin + "/" + name)) :::
    components.map(name =>
      "init_component " + quote(components_base) + "/" + name)
  }

  def resolve_components(echo: Boolean = false): Unit = {
    val missing = Path.split(getenv("ISABELLE_COMPONENTS_MISSING"))
    for (path <- missing) {
      Components.resolve(path.dir, path.file_name, ssh = ssh,
        progress = if (echo) progress else new Progress)
    }
  }

  def scala_build(fresh: Boolean = false, echo: Boolean = false): Unit = {
    if (fresh) ssh.rm_tree(isabelle_home + Path.explode("lib/classes"))

    val dummy_stty = Path.explode("~~/lib/dummy_stty/stty")
    val dummy_stty_remote = expand_path(dummy_stty)
    if (!ssh.is_file(dummy_stty_remote)) {
      ssh.make_directory(dummy_stty_remote.dir)
      ssh.write_file(dummy_stty_remote, dummy_stty)
      ssh.set_executable(dummy_stty_remote, true)
    }
    try {
      bash(
        "export PATH=\"" + bash_path(dummy_stty_remote.dir) + ":$PATH\"\n" +
        "export CLASSPATH=" + Bash.string(getenv("ISABELLE_CLASSPATH")) + "\n" +
        "bin/isabelle jedit -b", echo = echo).check
    }
    catch { case ERROR(msg) => cat_error("Failed to build Isabelle/Scala/Java modules:", msg) }
  }


  /* settings */

  def clean_settings(): Boolean =
    if (!ssh.is_file(etc_settings)) true
    else if (ssh.read(etc_settings).startsWith("# generated by Isabelle")) {
      ssh.delete(etc_settings)
      true
    }
    else false

  def init_settings(settings: List[String]): Unit = {
    if (clean_settings()) {
      ssh.make_directory(etc_settings.dir)
      ssh.write(etc_settings,
        "# generated by Isabelle " + Date.now() + "\n" +
        "#-*- shell-script -*- :mode=shellscript:\n" +
        settings.mkString("\n", "\n", "\n"))
    }
    else error("Cannot proceed with existing user settings file: " + etc_settings)
  }


  /* cleanup */

  def cleanup(): Unit = {
    clean_settings()
    ssh.delete(etc)
    ssh.delete(isabelle_home_user)
  }
}

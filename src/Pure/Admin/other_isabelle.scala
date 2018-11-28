/*  Title:      Pure/Admin/other_isabelle.scala
    Author:     Makarius

Manage other Isabelle distributions.
*/

package isabelle


object Other_Isabelle
{
  def apply(isabelle_home: Path,
      isabelle_identifier: String = "",
      user_home: Path = Path.explode("$USER_HOME"),
      progress: Progress = No_Progress): Other_Isabelle =
    new Other_Isabelle(isabelle_home, isabelle_identifier, user_home, progress)
}

class Other_Isabelle(
  val isabelle_home: Path,
  val isabelle_identifier: String,
  user_home: Path,
  progress: Progress)
{
  other_isabelle =>

  override def toString: String = isabelle_home.toString

  if (proper_string(System.getenv("ISABELLE_SETTINGS_PRESENT")).isDefined)
    error("Cannot initialize with enclosing ISABELLE_SETTINGS_PRESENT")


  /* static system */

  def bash(
      script: String,
      redirect: Boolean = false,
      echo: Boolean = false,
      strict: Boolean = true): Process_Result =
    progress.bash(
      "export USER_HOME=" + File.bash_path(user_home) + "\n" +
      Isabelle_System.export_isabelle_identifier(isabelle_identifier) + script,
      env = null, cwd = isabelle_home.file, redirect = redirect, echo = echo, strict = strict)

  def apply(
      cmdline: String,
      redirect: Boolean = false,
      echo: Boolean = false,
      strict: Boolean = true): Process_Result =
    bash("bin/isabelle " + cmdline, redirect = redirect, echo = echo, strict = strict)

  def resolve_components(echo: Boolean): Unit =
    other_isabelle("components -a", redirect = true, echo = echo).check

  def getenv(name: String): String =
    other_isabelle("getenv -b " + Bash.string(name)).check.out

  val isabelle_home_user: Path = Path.explode(getenv("ISABELLE_HOME_USER"))

  val etc: Path = isabelle_home_user + Path.explode("etc")
  val etc_settings: Path = etc + Path.explode("settings")
  val etc_preferences: Path = etc + Path.explode("preferences")

  def copy_fonts(target_dir: Path): Unit =
    Isabelle_Fonts.make_entries(getenv = getenv(_), html = true).
      foreach(entry => File.copy(entry.path, target_dir))


  /* settings */

  def clean_settings(): Boolean =
    if (!etc_settings.is_file) true
    else if (File.read(etc_settings).startsWith("# generated by Isabelle")) {
      etc_settings.file.delete; true
    }
    else false

  def init_settings(components_base: String, nonfree: Boolean, more_settings: List[String])
  {
    if (!clean_settings())
      error("Cannot proceed with existing user settings file: " + etc_settings)

    Isabelle_System.mkdirs(etc_settings.dir)
    File.write(etc_settings,
      "# generated by Isabelle " + Date.now() + "\n" +
      "#-*- shell-script -*- :mode=shellscript:\n")

    val component_settings =
    {
      val components_base_path =
        if (components_base == "") isabelle_home_user.dir + Path.explode("contrib")
        else Path.explode(components_base).expand

      val catalogs =
        if (nonfree) List("main", "optional", "nonfree") else List("main", "optional")

      catalogs.map(catalog =>
        "init_components " + File.bash_path(components_base_path) +
          " \"$ISABELLE_HOME/Admin/components/" + catalog + "\"")
    }

    val settings =
      List(component_settings) :::
      (if (more_settings.isEmpty) Nil else List(more_settings))

    File.append(etc_settings, "\n" + cat_lines(settings.map(terminate_lines(_))))
  }


  /* cleanup */

  def cleanup()
  {
    clean_settings()
    etc.file.delete
    isabelle_home_user.file.delete
  }
}

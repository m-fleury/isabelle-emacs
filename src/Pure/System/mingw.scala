/*  Title:      Pure/System/mingw.scala
    Author:     Makarius

Support for MSYS2/MinGW64 on Windows.
*/

package isabelle


object MinGW {
  def environment: List[String] =
    List("PATH=/usr/bin:/bin:/mingw64/bin", "CONFIG_SITE=/mingw64/etc/config.site")

  def environment_export: String =
    environment.map(a => "export " + Bash.string(a)).mkString("", "\n", "\n")

  val none: MinGW = new MinGW(None)
  def apply(path: Path) = new MinGW(Some(path))
}

class MinGW private(val root: Option[Path]) {
  override def toString: String =
    root match {
      case None => "MinGW.none"
      case Some(msys_root) => "MinGW(" + msys_root.toString + ")"
    }

  def bash_script(script: String): String =
    root match {
      case None => script
      case Some(msys_root) =>
        File.bash_path(msys_root + Path.explode("usr/bin/bash")) +
          " -c " + Bash.string(MinGW.environment_export + script)
    }

  def get_root: Path =
    if (!Platform.is_windows) error("Windows platform required")
    else if (root.isEmpty) error("Windows platform requires msys/mingw root specification")
    else root.get

  def check: Unit = {
    if (Platform.is_windows) {
      get_root
      try { require(Isabelle_System.bash(bash_script("uname -s")).check.out.startsWith("MSYS")) }
      catch { case ERROR(msg) => cat_error("Bad msys/mingw installation " + get_root, msg) }
    }
  }
}

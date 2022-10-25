/*  Title:      Pure/General/xz.scala
    Author:     Makarius

Support for Zstd data compression.
*/

package isabelle


import com.github.luben.zstd


object Zstd {
  def init(): Unit = init_jni

  private lazy val init_jni: Unit = {
    require(!zstd.util.Native.isLoaded(),
      "Zstd library already initialized by other means than isabelle.Zstd.init()")

    val lib_dir = Path.explode("$ISABELLE_ZSTD_HOME/" + Platform.jvm_platform)
    val lib_file =
      File.find_files(lib_dir.file) match {
        case List(file) => file
        case _ => error("Exactly one file expected in directory " + lib_dir.expand)
      }
    System.load(File.platform_path(lib_file.getAbsolutePath))

    zstd.util.Native.assumeLoaded()
    assert(zstd.util.Native.isLoaded())
    Class.forName("com.github.luben.zstd.Zstd")
  }
}

/*  Title:      Pure/General/ssh.scala
    Author:     Makarius

SSH client based on JSch (see also http://www.jcraft.com/jsch/examples).
*/

package isabelle


import java.util.{Map => JMap}
import java.io.{InputStream, OutputStream, ByteArrayOutputStream}

import scala.collection.mutable
import scala.util.matching.Regex

import com.jcraft.jsch.{JSch, Logger => JSch_Logger, Session => JSch_Session, SftpException,
  OpenSSHConfig, UserInfo, ChannelExec, ChannelSftp, SftpATTRS, JSchException}


object SSH {
  /* target machine: user@host syntax */

  object Target {
    val User_Host: Regex = "^([^@]+)@(.+)$".r

    def parse(s: String): (String, String) =
      s match {
        case User_Host(user, host) => (user, host)
        case _ => ("", s)
      }

    def unapplySeq(s: String): Option[List[String]] =
      parse(s) match {
        case (_, "") => None
        case (user, host) => Some(List(user, host))
      }
  }

  val default_port = 22
  def make_port(port: Int): Int = if (port > 0) port else default_port

  def port_suffix(port: Int): String =
    if (port == default_port) "" else ":" + port

  def user_prefix(user: String): String =
    proper_string(user) match {
      case None => ""
      case Some(name) => name + "@"
    }

  def connect_timeout(options: Options): Int =
    options.seconds("ssh_connect_timeout").ms.toInt

  def alive_interval(options: Options): Int =
    options.seconds("ssh_alive_interval").ms.toInt

  def alive_count_max(options: Options): Int =
    options.int("ssh_alive_count_max")


  /* open session */

  private def connect_session(
    options: Options,
    jsch: JSch,
    host: String,
    user: String = "",
    port: Int = 0,
    permissive: Boolean = false,
    nominal_host: String = "",
    nominal_user: String = "",
    nominal_port: Option[Int] = None,
    on_close: () => Unit = () => ()
  ): Session = {
    val connect_port = make_port(port)
    val session = jsch.getSession(proper_string(user).orNull, host, connect_port)

    session.setUserInfo(No_User_Info)
    session.setServerAliveInterval(alive_interval(options))
    session.setServerAliveCountMax(alive_count_max(options))
    session.setConfig("MaxAuthTries", "3")
    if (permissive) session.setConfig("StrictHostKeyChecking", "no")
    if (nominal_host != "") session.setHostKeyAlias(nominal_host)

    if (options.bool("ssh_compression")) {
      session.setConfig("compression.s2c", "zlib@openssh.com,zlib,none")
      session.setConfig("compression.c2s", "zlib@openssh.com,zlib,none")
      session.setConfig("compression_level", "9")
    }
    session.connect(connect_timeout(options))
    new Session(options, session, on_close,
      proper_string(nominal_host) getOrElse host,
      proper_string(nominal_user) getOrElse user,
      nominal_port getOrElse connect_port)
  }

  def open_session(
    options: Options,
    host: String,
    user: String = "",
    port: Int = 0,
    actual_host: String = "",
    proxy_host: String = "",
    proxy_user: String = "",
    proxy_port: Int = 0,
    permissive: Boolean = false
  ): Session = {
    val config_dir = Path.explode(options.string("ssh_config_dir"))
    if (!config_dir.is_dir) error("Bad ssh config directory: " + config_dir)

    val jsch = new JSch

    val config_file = Path.explode(options.string("ssh_config_file"))
    if (config_file.is_file)
      jsch.setConfigRepository(OpenSSHConfig.parseFile(File.platform_path(config_file)))

    val known_hosts = config_dir + Path.explode("known_hosts")
    if (!known_hosts.is_file) known_hosts.file.createNewFile
    jsch.setKnownHosts(File.platform_path(known_hosts))

    val identity_files =
      space_explode(':', options.string("ssh_identity_files")).map(Path.explode)
    for (identity_file <- identity_files if identity_file.is_file) {
      try { jsch.addIdentity(File.platform_path(identity_file)) }
      catch {
        case exn: JSchException =>
          error("Error in ssh identity file " + identity_file + ": " + exn.getMessage)
      }
    }

    val connect_host = proper_string(actual_host) getOrElse host
    val connect_port = make_port(port)
    if (proxy_host == "") {
      connect_session(options, jsch, host = connect_host, user = user, port = connect_port)
    }
    else {
      val proxy =
        connect_session(options, jsch, host = proxy_host, port = proxy_port, user = proxy_user)

      val fw =
        try { proxy.port_forwarding(remote_host = connect_host, remote_port = connect_port) }
        catch { case exn: Throwable => proxy.close(); throw exn }

      try {
        connect_session(options, jsch,
          host = fw.local_host,
          port = fw.local_port,
          permissive = permissive,
          nominal_host = host,
          nominal_port = Some(connect_port),
          nominal_user = user, user = user,
          on_close = { () => fw.close(); proxy.close() })
      }
      catch { case exn: Throwable => fw.close(); proxy.close(); throw exn }
    }
  }


  /* user info */

  object No_User_Info extends UserInfo {
    def getPassphrase: String = null
    def getPassword: String = null
    def promptPassword(msg: String): Boolean = false
    def promptPassphrase(msg: String): Boolean = false
    def promptYesNo(msg: String): Boolean = false
    def showMessage(msg: String): Unit = Output.writeln(msg)
  }


  /* Sftp channel */

  type Attrs = SftpATTRS

  sealed case class Dir_Entry(name: String, is_dir: Boolean) {
    def is_file: Boolean = !is_dir
  }


  /* exec channel */

  private val exec_wait_delay = Time.seconds(0.3)

  class Exec private[SSH](session: Session, channel: ChannelExec) extends AutoCloseable {
    override def toString: String = "exec " + session.toString

    def close(): Unit = channel.disconnect()

    val exit_status: Future[Int] =
      Future.thread("ssh_wait") {
        while (!channel.isClosed) exec_wait_delay.sleep()
        channel.getExitStatus
      }

    val stdin: OutputStream = channel.getOutputStream
    val stdout: InputStream = channel.getInputStream
    val stderr: InputStream = channel.getErrStream

    // connect after preparing streams
    channel.connect(connect_timeout(session.options))

    def result(
      progress_stdout: String => Unit = (_: String) => (),
      progress_stderr: String => Unit = (_: String) => (),
      strict: Boolean = true
    ): Process_Result = {
      stdin.close()

      def read_lines(stream: InputStream, progress: String => Unit): List[String] = {
        val result = new mutable.ListBuffer[String]
        val line_buffer = new ByteArrayOutputStream(100)
        def line_flush(): Unit = {
          val line = Library.trim_line(line_buffer.toString(UTF8.charset_name))
          progress(line)
          result += line
          line_buffer.reset()
        }

        var c = 0
        var finished = false
        while (!finished) {
          while ({ c = stream.read; c != -1 && c != 10 }) line_buffer.write(c)
          if (c == 10) line_flush()
          else if (channel.isClosed) {
            if (line_buffer.size > 0) line_flush()
            finished = true
          }
          else exec_wait_delay.sleep()
        }

        result.toList
      }

      val out_lines = Future.thread("ssh_stdout") { read_lines(stdout, progress_stdout) }
      val err_lines = Future.thread("ssh_stderr") { read_lines(stderr, progress_stderr) }

      def terminate(): Unit = {
        close()
        out_lines.join
        err_lines.join
        exit_status.join
      }

      val rc =
        try { exit_status.join }
        catch { case Exn.Interrupt() => terminate(); Process_Result.RC.interrupt }

      close()
      if (strict && rc == Process_Result.RC.interrupt) throw Exn.Interrupt()

      Process_Result(rc, out_lines.join, err_lines.join)
    }
  }


  /* session */

  class Session private[SSH](
    val options: Options,
    session: JSch_Session,
    on_close: () => Unit,
    val nominal_host: String,
    val nominal_user: String,
    val nominal_port: Int
  ) extends System {
    ssh =>

    def host: String = if (session.getHost == null) "" else session.getHost

    override def hg_url: String =
      "ssh://" + user_prefix(nominal_user) + nominal_host + "/"

    override def rsync_prefix: String =
      user_prefix(nominal_user) + nominal_host + ":"

    override def toString: String =
      user_prefix(session.getUserName) + host + port_suffix(session.getPort) +
      (if (session.isConnected) "" else " (disconnected)")


    /* port forwarding */

    def port_forwarding(
      remote_port: Int,
      remote_host: String = "localhost",
      local_port: Int = 0,
      local_host: String = "localhost",
      ssh_close: Boolean = false
    ): Port_Forwarding = {
      val local_port1 = session.setPortForwardingL(local_host, local_port, remote_host, remote_port)
      new Port_Forwarding(local_host, local_port1, remote_host, remote_port) {
        override def close(): Unit = {
          session.delPortForwardingL(this.local_host, this.local_port)
          if (ssh_close) ssh.close()
        }
      }
    }


    /* sftp channel */

    private val sftp: ChannelSftp = session.openChannel("sftp").asInstanceOf[ChannelSftp]
    sftp.connect(connect_timeout(options))

    override def close(): Unit = { sftp.disconnect(); session.disconnect(); on_close() }

    val settings: JMap[String, String] = {
      val home = sftp.getHome
      JMap.of("HOME", home, "USER_HOME", home)
    }
    override def expand_path(path: Path): Path = path.expand_env(settings)
    def remote_path(path: Path): String = expand_path(path).implode
    override def bash_path(path: Path): String = Bash.string(remote_path(path))

    def chmod(permissions: Int, path: Path): Unit = sftp.chmod(permissions, remote_path(path))
    def rm(path: Path): Unit = sftp.rm(remote_path(path))
    def mkdir(path: Path): Unit = sftp.mkdir(remote_path(path))

    private def test_entry(path: Path, as_dir: Boolean): Boolean =
      try {
        val is_dir = sftp.stat(remote_path(path)).isDir
        if (as_dir) is_dir else !is_dir
      }
      catch { case _: SftpException => false }

    override def is_dir(path: Path): Boolean = test_entry(path, true)
    override def is_file(path: Path): Boolean = test_entry(path, false)

    override def make_directory(path: Path): Path = {
      if (!is_dir(path)) {
        execute(
          "perl -e \"use File::Path make_path; make_path('" + remote_path(path) + "');\"")
        if (!is_dir(path)) error("Failed to create directory: " + quote(remote_path(path)))
      }
      path
    }

    def read_dir(path: Path): List[Dir_Entry] = {
      if (!is_dir(path)) error("No such directory: " + path.toString)

      val dir_name = remote_path(path)
      val dir = sftp.ls(dir_name)
      (for {
        i <- (0 until dir.size).iterator
        a = dir.get(i).asInstanceOf[AnyRef]
        name = Untyped.get[String](a, "filename")
        attrs = Untyped.get[Attrs](a, "attrs")
        if name != "." && name != ".."
      }
      yield {
        Dir_Entry(name,
          if (attrs.isLink) {
            try { sftp.stat(dir_name + "/" + name).isDir }
            catch { case _: SftpException => false }
          }
          else attrs.isDir)
      }).toList.sortBy(_.name)
    }

    def open_input(path: Path): InputStream = sftp.get(remote_path(path))
    def open_output(path: Path): OutputStream = sftp.put(remote_path(path))

    override def read_file(path: Path, local_path: Path): Unit =
      sftp.get(remote_path(path), File.platform_path(local_path))
    override def read_bytes(path: Path): Bytes = using(open_input(path))(Bytes.read_stream(_))
    override def read(path: Path): String = using(open_input(path))(File.read_stream)

    override def write_file(path: Path, local_path: Path): Unit =
      sftp.put(File.platform_path(local_path), remote_path(path))
    def write_bytes(path: Path, bytes: Bytes): Unit =
      using(open_output(path))(bytes.write_stream)
    def write(path: Path, text: String): Unit =
      using(open_output(path))(stream => Bytes(text).write_stream(stream))


    /* exec channel */

    def exec(command: String): Exec = {
      val channel = session.openChannel("exec").asInstanceOf[ChannelExec]
      channel.setCommand("export USER_HOME=\"$HOME\"\n" + command)
      new Exec(this, channel)
    }

    override def execute(command: String,
        progress_stdout: String => Unit = (_: String) => (),
        progress_stderr: String => Unit = (_: String) => (),
        settings: Boolean = true,
        strict: Boolean = true): Process_Result =
      exec(command).result(progress_stdout, progress_stderr, strict)

    override def isabelle_platform: Isabelle_Platform = Isabelle_Platform(ssh = Some(this))


    /* tmp dirs */

    def rm_tree(dir: Path): Unit = rm_tree(remote_path(dir))

    def rm_tree(remote_dir: String): Unit =
      execute("rm -r -f " + Bash.string(remote_dir)).check

    def tmp_dir(): String =
      execute("mktemp -d -t tmp.XXXXXXXXXX").check.out

    override def with_tmp_dir[A](body: Path => A): A = {
      val remote_dir = tmp_dir()
      try { body(Path.explode(remote_dir)) } finally { rm_tree(remote_dir) }
    }
  }

  abstract class Port_Forwarding private[SSH](
    val local_host: String,
    val local_port: Int,
    val remote_host: String,
    val remote_port: Int
  ) extends AutoCloseable {
    override def toString: String =
      local_host + ":" + local_port + ":" + remote_host + ":" + remote_port
  }


  /* system operations */

  trait System extends AutoCloseable {
    def close(): Unit = ()

    def hg_url: String = ""

    def rsync_prefix: String = ""
    def rsync_path(path: Path): String = rsync_prefix + expand_path(path).implode

    def expand_path(path: Path): Path = path.expand
    def bash_path(path: Path): String = File.bash_path(path)
    def is_dir(path: Path): Boolean = path.is_dir
    def is_file(path: Path): Boolean = path.is_file
    def make_directory(path: Path): Path = Isabelle_System.make_directory(path)
    def with_tmp_dir[A](body: Path => A): A = Isabelle_System.with_tmp_dir("tmp")(body)
    def read_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path1, path2)
    def write_file(path1: Path, path2: Path): Unit = Isabelle_System.copy_file(path2, path1)
    def read_bytes(path: Path): Bytes = Bytes.read(path)
    def read(path: Path): String = File.read(path)

    def execute(command: String,
        progress_stdout: String => Unit = (_: String) => (),
        progress_stderr: String => Unit = (_: String) => (),
        settings: Boolean = true,
        strict: Boolean = true): Process_Result =
      Isabelle_System.bash(command,
        progress_stdout = progress_stdout,
        progress_stderr = progress_stderr,
        env = if (settings) Isabelle_System.settings() else null,
        strict = strict)

    def isabelle_platform: Isabelle_Platform = Isabelle_Platform()
  }

  object Local extends System
}

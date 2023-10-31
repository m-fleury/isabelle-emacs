/*  Title:      Pure/Admin/build_log.scala
    Author:     Makarius

Management of build log files and database storage.
*/

package isabelle


import java.io.{File => JFile}
import java.time.format.{DateTimeFormatter, DateTimeParseException}
import java.util.Locale

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import scala.util.matching.Regex


object Build_Log {
  /** content **/

  /* properties */

  object Prop {
    val build_tags = SQL.Column.string("build_tags")  // lines
    val build_args = SQL.Column.string("build_args")  // lines
    val build_group_id = SQL.Column.string("build_group_id")
    val build_id = SQL.Column.string("build_id")
    val build_engine = SQL.Column.string("build_engine")
    val build_host = SQL.Column.string("build_host")
    val build_start = SQL.Column.date("build_start")
    val build_end = SQL.Column.date("build_end")
    val isabelle_version = SQL.Column.string("isabelle_version")
    val afp_version = SQL.Column.string("afp_version")

    val all_props: List[SQL.Column] =
      List(build_tags, build_args, build_group_id, build_id, build_engine,
        build_host, build_start, build_end, isabelle_version, afp_version)
  }


  /* settings */

  object Settings {
    val ISABELLE_BUILD_OPTIONS = SQL.Column.string("ISABELLE_BUILD_OPTIONS")
    val ML_PLATFORM = SQL.Column.string("ML_PLATFORM")
    val ML_HOME = SQL.Column.string("ML_HOME")
    val ML_SYSTEM = SQL.Column.string("ML_SYSTEM")
    val ML_OPTIONS = SQL.Column.string("ML_OPTIONS")

    val ml_settings = List(ML_PLATFORM, ML_HOME, ML_SYSTEM, ML_OPTIONS)
    val all_settings = ISABELLE_BUILD_OPTIONS :: ml_settings

    type Entry = (String, String)
    type T = List[Entry]

    object Entry {
      def unapply(s: String): Option[Entry] =
        for { (a, b) <- Properties.Eq.unapply(s) }
        yield (a, Library.perhaps_unquote(b))
      def getenv(a: String): String =
        Properties.Eq(a, quote(Isabelle_System.getenv(a)))
    }

    def show(): String =
      cat_lines(
        List(Entry.getenv("ISABELLE_TOOL_JAVA_OPTIONS"),
          Entry.getenv(ISABELLE_BUILD_OPTIONS.name), "") :::
        ml_settings.map(c => Entry.getenv(c.name)))
  }


  /* file names */

  def log_date(date: Date): String =
    String.format(Locale.ROOT, "%s.%05d",
      DateTimeFormatter.ofPattern("yyyy-MM-dd").format(date.rep),
      java.lang.Long.valueOf((date.time - date.midnight.time).ms / 1000))

  def log_subdir(date: Date): Path =
    Path.explode("log") + Path.explode(date.rep.getYear.toString)

  def log_filename(engine: String, date: Date, more: List[String] = Nil): Path =
    Path.explode((engine :: log_date(date) :: more).mkString("", "_", ".log"))



  /** log file **/

  def print_date(date: Date): String = Log_File.Date_Format(date)

  object Log_File {
    /* log file */

    val all_suffixes: List[String] = List(".log", ".log.gz", ".log.xz", ".gz", ".xz")

    def plain_name(name: String): String = {
      all_suffixes.find(name.endsWith) match {
        case Some(s) => Library.try_unsuffix(s, name).get
        case None => name
      }
    }
    def plain_name(file: JFile): String = plain_name(file.getName)

    def apply(name: String, lines: List[String]): Log_File =
      new Log_File(plain_name(name), lines.map(Library.trim_line))

    def apply(name: String, text: String): Log_File =
      new Log_File(plain_name(name), Library.trim_split_lines(text))

    def apply(file: JFile): Log_File = {
      val name = file.getName
      val text =
        if (File.is_gz(name)) File.read_gzip(file)
        else if (File.is_xz(name)) File.read_xz(file)
        else File.read(file)
      apply(name, text)
    }

    def apply(path: Path): Log_File = apply(path.file)


    /* log file collections */

    val log_prefixes: List[String] =
      List(Build_History.log_prefix, Identify.log_prefix, Identify.log_prefix2,
        Isatest.log_prefix, AFP_Test.log_prefix)

    val log_suffixes: List[String] = List(".log", ".log.gz", ".log.xz")

    def is_log(file: JFile,
      prefixes: List[String] = log_prefixes,
      suffixes: List[String] = log_suffixes
    ): Boolean = {
      val name = file.getName

      prefixes.exists(name.startsWith) &&
      suffixes.exists(name.endsWith) &&
      name != "isatest.log" &&
      name != "afp-test.log" &&
      name != "main.log"
    }

    def find_files(starts: List[JFile]): List[JFile] =
      starts.flatMap(start => File.find_files(start, pred = is_log(_), follow_links = true))
        .sortBy(plain_name)


    /* date format */

    val Date_Format = {
      val fmts =
        Date.Formatter.variants(
          List("EEE MMM d HH:mm:ss O yyyy", "EEE MMM d HH:mm:ss VV yyyy"),
          List(Locale.ENGLISH, Locale.GERMAN)) :::
        List(
          DateTimeFormatter.RFC_1123_DATE_TIME,
          Date.Formatter.pattern("EEE MMM d HH:mm:ss yyyy").withZone(Date.timezone_berlin))

      def tune_timezone(s: String): String =
        s match {
          case "CET" | "MET" => "GMT+1"
          case "CEST" | "MEST" => "GMT+2"
          case "EST" => "Europe/Berlin"
          case _ => s
        }
      def tune_weekday(s: String): String =
        s match {
          case "Die" => "Di"
          case "Mit" => "Mi"
          case "Don" => "Do"
          case "Fre" => "Fr"
          case "Sam" => "Sa"
          case "Son" => "So"
          case _ => s
        }

      def tune(s: String): String =
        Word.implode(
          Word.explode(s) match {
            case a :: "M\uFFFDr" :: bs => tune_weekday(a) :: "Mär" :: bs.map(tune_timezone)
            case a :: bs => tune_weekday(a) :: bs.map(tune_timezone)
            case Nil => Nil
          }
        )

      Date.Format.make(fmts, tune)
    }
  }

  class Log_File private(val name: String, val lines: List[String]) {
    log_file =>

    override def toString: String = name

    def text: String = cat_lines(lines)

    def err(msg: String): Nothing =
      error("Bad log file " + quote(name) + ": " + msg)


    /* date format */

    object Strict_Date {
      def unapply(s: String): Some[Date] =
        try { Some(Log_File.Date_Format.parse(s)) }
        catch { case exn: DateTimeParseException => log_file.err(exn.getMessage) }
    }


    /* inlined text */

    def filter(Marker: Protocol_Message.Marker): List[String] =
      for (case Marker(text) <- lines) yield text

    def find(Marker: Protocol_Message.Marker): Option[String] =
      lines.collectFirst({ case Marker(text) => text })

    def find_match(regexes: List[Regex]): Option[String] =
      regexes match {
        case Nil => None
        case regex :: rest =>
          lines.iterator.map(regex.unapplySeq(_)).find(res => res.isDefined && res.get.length == 1).
            map(res => res.get.head) orElse find_match(rest)
      }


    /* settings */

    def get_setting(name: String): Option[Settings.Entry] =
      lines.collectFirst({ case Settings.Entry(a, b) if a == name => a -> b })

    def get_all_settings: Settings.T =
      for { c <- Settings.all_settings; entry <- get_setting(c.name) }
      yield entry


    /* properties (YXML) */

    val cache: XML.Cache = XML.Cache.make()

    def parse_props(text: String): Properties.T =
      try { cache.props(XML.Decode.properties(YXML.parse_body(text))) }
      catch { case _: XML.Error => log_file.err("malformed properties") }

    def filter_props(marker: Protocol_Message.Marker): List[Properties.T] =
      for (text <- filter(marker) if YXML.detect(text)) yield parse_props(text)

    def find_props(marker: Protocol_Message.Marker): Option[Properties.T] =
      for (text <- find(marker) if YXML.detect(text)) yield parse_props(text)


    /* parse various formats */

    def parse_meta_info(): Meta_Info = Build_Log.parse_meta_info(log_file)

    def parse_build_info(ml_statistics: Boolean = false): Build_Info =
      Build_Log.parse_build_info(log_file, ml_statistics)

    def parse_session_info(
        command_timings: Boolean = false,
        theory_timings: Boolean = false,
        ml_statistics: Boolean = false,
        task_statistics: Boolean = false): Session_Info =
      Build_Log.parse_session_info(
        log_file, command_timings, theory_timings, ml_statistics, task_statistics)
  }



  /** digested meta info: produced by Admin/build_other in log.xz file **/

  object Meta_Info {
    val empty: Meta_Info = Meta_Info(Nil, Nil)
  }

  sealed case class Meta_Info(props: Properties.T, settings: Settings.T) {
    def is_empty: Boolean = props.isEmpty && settings.isEmpty

    def get(c: SQL.Column): Option[String] =
      Properties.get(props, c.name) orElse
      Properties.get(settings, c.name)

    def get_date(c: SQL.Column): Option[Date] =
      get(c).map(Log_File.Date_Format.parse)
  }

  object Identify {
    val log_prefix = "isabelle_identify_"
    val log_prefix2 = "plain_identify_"

    def engine(log_file: Log_File): String =
      if (log_file.name.startsWith(log_prefix2)) "plain_identify" else "identify"

    def content(date: Date, isabelle_version: Option[String], afp_version: Option[String]): String =
      terminate_lines(
        List("isabelle_identify: " + Build_Log.print_date(date), "") :::
        isabelle_version.map("Isabelle version: " + _).toList :::
        afp_version.map("AFP version: " + _).toList)

    val Start = new Regex("""^isabelle_identify: (.+)$""")
    val No_End = new Regex("""$.""")
    val Isabelle_Version = List(new Regex("""^Isabelle version: (\S+)$"""))
    val AFP_Version = List(new Regex("""^AFP version: (\S+)$"""))
  }

  object Isatest {
    val log_prefix = "isatest-makeall-"
    val engine = "isatest"
    val Start = new Regex("""^------------------- starting test --- (.+) --- (.+)$""")
    val End = new Regex("""^------------------- test (?:successful|FAILED) --- (.+) --- .*$""")
    val Isabelle_Version = List(new Regex("""^Isabelle version: (\S+)$"""))
  }

  object AFP_Test {
    val log_prefix = "afp-test-devel-"
    val engine = "afp-test"
    val Start = new Regex("""^Start test(?: for .+)? at ([^,]+), (.*)$""")
    val Start_Old = new Regex("""^Start test(?: for .+)? at ([^,]+)$""")
    val End = new Regex("""^End test on (.+), .+, elapsed time:.*$""")
    val Isabelle_Version = List(new Regex("""^Isabelle version: .* -- hg id (\S+)$"""))
    val AFP_Version = List(new Regex("""^AFP version: .* -- hg id (\S+)$"""))
    val Bad_Init = new Regex("""^cp:.*: Disc quota exceeded$""")
  }

  object Jenkins {
    val log_prefix = "jenkins_"
    val engine = "jenkins"
    val Host = new Regex("""^Building remotely on (\S+) \((\S+)\).*$""")
    val Start = new Regex("""^(?:Started by an SCM change|Started from command line by admin|).*$""")
    val Start_Date = new Regex("""^Build started at (.+)$""")
    val No_End = new Regex("""$.""")
    val Isabelle_Version =
      List(new Regex("""^(?:Build for Isabelle id|Isabelle id) (\w+).*$"""),
        new Regex("""^ISABELLE_CI_REPO_ID="(\w+)".*$"""),
        new Regex("""^(\w{12}) tip.*$"""))
    val AFP_Version =
      List(new Regex("""^(?:Build for AFP id|AFP id) (\w+).*$"""),
        new Regex("""^ISABELLE_CI_AFP_ID="(\w+)".*$"""))
    val CONFIGURATION = "=== CONFIGURATION ==="
    val BUILD = "=== BUILD ==="
  }

  private def parse_meta_info(log_file: Log_File): Meta_Info = {
    def parse(engine: String, host: String, start: Date,
      End: Regex, Isabelle_Version: List[Regex], AFP_Version: List[Regex]
    ): Meta_Info = {
      val build_id = {
        val prefix = proper_string(host) orElse proper_string(engine) getOrElse "build"
        prefix + ":" + start.time.ms
      }
      val build_engine = if (engine == "") Nil else List(Prop.build_engine.name -> engine)
      val build_host = if (host == "") Nil else List(Prop.build_host.name -> host)

      val start_date = List(Prop.build_start.name -> print_date(start))
      val end_date =
        log_file.lines.last match {
          case End(log_file.Strict_Date(end_date)) =>
            List(Prop.build_end.name -> print_date(end_date))
          case _ => Nil
        }

      val isabelle_version =
        log_file.find_match(Isabelle_Version).map(Prop.isabelle_version.name -> _)
      val afp_version =
        log_file.find_match(AFP_Version).map(Prop.afp_version.name -> _)

      Meta_Info((Prop.build_id.name -> build_id) :: build_engine ::: build_host :::
          start_date ::: end_date ::: isabelle_version.toList ::: afp_version.toList,
        log_file.get_all_settings)
    }

    log_file.lines match {
      case line :: _ if Protocol.Meta_Info_Marker.test_yxml(line) =>
        Meta_Info(log_file.find_props(Protocol.Meta_Info_Marker).get, log_file.get_all_settings)

      case Identify.Start(log_file.Strict_Date(start)) :: _ =>
        parse(Identify.engine(log_file), "", start, Identify.No_End,
          Identify.Isabelle_Version, Identify.AFP_Version)

      case Isatest.Start(log_file.Strict_Date(start), host) :: _ =>
        parse(Isatest.engine, host, start, Isatest.End,
          Isatest.Isabelle_Version, Nil)

      case AFP_Test.Start(log_file.Strict_Date(start), host) :: _ =>
        parse(AFP_Test.engine, host, start, AFP_Test.End,
          AFP_Test.Isabelle_Version, AFP_Test.AFP_Version)

      case AFP_Test.Start_Old(log_file.Strict_Date(start)) :: _ =>
        parse(AFP_Test.engine, "", start, AFP_Test.End,
          AFP_Test.Isabelle_Version, AFP_Test.AFP_Version)

      case line :: _ if line.startsWith("\u0000") => Meta_Info.empty
      case List(Isatest.End(_)) => Meta_Info.empty
      case _ :: AFP_Test.Bad_Init() :: _ => Meta_Info.empty
      case Nil => Meta_Info.empty

      case _ => log_file.err("cannot detect log file format")
    }
  }



  /** build info: toplevel output of isabelle build or Admin/build_other **/

  val SESSION_NAME = "session_name"

  enum Session_Status { case existing, finished, failed, cancelled }

  sealed case class Session_Entry(
    chapter: String = "",
    groups: List[String] = Nil,
    hostname: Option[String] = None,
    threads: Option[Int] = None,
    timing: Timing = Timing.zero,
    ml_timing: Timing = Timing.zero,
    sources: Option[String] = None,
    heap_size: Option[Space] = None,
    status: Option[Session_Status] = None,
    errors: List[String] = Nil,
    theory_timings: Map[String, Timing] = Map.empty,
    ml_statistics: List[Properties.T] = Nil
  ) {
    def proper_groups: Option[String] = if (groups.isEmpty) None else Some(cat_lines(groups))
    def finished: Boolean = status == Some(Session_Status.finished)
    def failed: Boolean = status == Some(Session_Status.failed)
  }

  object Build_Info {
    val sessions_dummy: Map[String, Session_Entry] =
      Map("" -> Session_Entry(theory_timings = Map("" -> Timing.zero)))
  }

  sealed case class Build_Info(sessions: Map[String, Session_Entry]) {
    def finished_sessions: List[String] = for ((a, b) <- sessions.toList if b.finished) yield a
    def failed_sessions: List[String] = for ((a, b) <- sessions.toList if b.failed) yield a
  }

  private def parse_build_info(log_file: Log_File, parse_ml_statistics: Boolean): Build_Info = {
    object Chapter_Name {
      def unapply(s: String): Some[(String, String)] =
        space_explode('/', s) match {
          case List(chapter, name) => Some((chapter, name))
          case _ => Some(("", s))
        }
    }

    val Session_No_Groups = new Regex("""^Session (\S+)$""")
    val Session_Groups = new Regex("""^Session (\S+) \((.*)\)$""")
    val Session_Finished1 =
      new Regex("""^Finished (\S+) \((\d+):(\d+):(\d+) elapsed time, (\d+):(\d+):(\d+) cpu time.*$""")
    val Session_Finished2 =
      new Regex("""^Finished ([^\s/]+) \((\d+):(\d+):(\d+) elapsed time.*$""")
    val Session_Timing =
      new Regex("""^Timing (\S+) \((\d+) threads, (\d+\.\d+)s elapsed time, (\d+\.\d+)s cpu time, (\d+\.\d+)s GC time.*$""")
    val Session_Started1 = new Regex("""^(?:Running|Building) (\S+) \.\.\.$""")
    val Session_Started2 = new Regex("""^(?:Running|Building) (\S+) \(?on ([^\s/]+)/?(\d+)\+?(\S+)\)? \.\.\.$""")
    val Sources = new Regex("""^Sources (\S+) (\S{""" + SHA1.digest_length + """})$""")
    val Heap = new Regex("""^Heap (\S+) \((\d+) bytes\)$""")

    object Theory_Timing {
      def unapply(line: String): Option[(String, (String, Timing))] =
        Protocol.Theory_Timing_Marker.unapply(line.replace('~', '-')).map(log_file.parse_props)
        match {
          case Some((SESSION_NAME, session) :: props) =>
            for (theory <- Markup.Name.unapply(props))
            yield (session, theory -> Markup.Timing_Properties.get(props))
          case _ => None
        }
    }

    var chapter = Map.empty[String, String]
    var groups = Map.empty[String, List[String]]
    var hostnames = Map.empty[String, String]
    var threads = Map.empty[String, Int]
    var timing = Map.empty[String, Timing]
    var ml_timing = Map.empty[String, Timing]
    var started = Set.empty[String]
    var sources = Map.empty[String, String]
    var heap_sizes = Map.empty[String, Space]
    var theory_timings = Map.empty[String, Map[String, Timing]]
    var ml_statistics = Map.empty[String, List[Properties.T]]
    var errors = Map.empty[String, List[String]]

    def all_sessions: Set[String] =
      chapter.keySet ++ groups.keySet ++ threads.keySet ++ timing.keySet ++ ml_timing.keySet ++
      started ++ sources.keySet ++ heap_sizes.keySet ++
      theory_timings.keySet ++ ml_statistics.keySet


    for (line <- log_file.lines) {
      line match {
        case Session_No_Groups(Chapter_Name(chapt, name)) =>
          chapter += (name -> chapt)
          groups += (name -> Nil)

        case Session_Groups(Chapter_Name(chapt, name), grps) =>
          chapter += (name -> chapt)
          groups += (name -> Word.explode(grps))

        case Session_Started1(name) =>
          started += name

        case Session_Started2(name, hostname, numa_node, rel_cpus) =>
          started += name
          hostnames += (name -> hostname)

        case Session_Finished1(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3),
            Value.Int(c1), Value.Int(c2), Value.Int(c3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          val cpu = Time.hms(c1, c2, c3)
          timing += (name -> Timing(elapsed, cpu, Time.zero))

        case Session_Finished2(name,
            Value.Int(e1), Value.Int(e2), Value.Int(e3)) =>
          val elapsed = Time.hms(e1, e2, e3)
          timing += (name -> Timing(elapsed, Time.zero, Time.zero))

        case Session_Timing(name,
            Value.Int(t), Value.Double(e), Value.Double(c), Value.Double(g)) =>
          val elapsed = Time.seconds(e)
          val cpu = Time.seconds(c)
          val gc = Time.seconds(g)
          ml_timing += (name -> Timing(elapsed, cpu, gc))
          threads += (name -> t)

        case Sources(name, s) =>
          sources += (name -> s)

        case Heap(name, Value.Long(size)) =>
          heap_sizes += (name -> Space.bytes(size))

        case _ if Protocol.Theory_Timing_Marker.test_yxml(line) =>
          line match {
            case Theory_Timing(name, theory_timing) =>
              theory_timings += (name -> (theory_timings.getOrElse(name, Map.empty) + theory_timing))
            case _ => log_file.err("malformed theory_timing " + quote(line))
          }

        case _ if parse_ml_statistics && Protocol.ML_Statistics_Marker.test_yxml(line) =>
          Protocol.ML_Statistics_Marker.unapply(line).map(log_file.parse_props) match {
            case Some((SESSION_NAME, name) :: props) =>
              ml_statistics += (name -> (props :: ml_statistics.getOrElse(name, Nil)))
            case _ => log_file.err("malformed ML_statistics " + quote(line))
          }

        case _ if Protocol.Error_Message_Marker.test_yxml(line) =>
          Protocol.Error_Message_Marker.unapply(line).map(log_file.parse_props) match {
            case Some(List((SESSION_NAME, name), (Markup.CONTENT, msg))) =>
              errors += (name -> (msg :: errors.getOrElse(name, Nil)))
            case _ => log_file.err("malformed error message " + quote(line))
          }

        case _ =>
      }
    }

    val sessions =
      Map(
        (for (name <- all_sessions.toList) yield {
          val status =
            if (timing.isDefinedAt(name) || ml_timing.isDefinedAt(name))
              Session_Status.finished
            else if (started(name)) Session_Status.failed
            else Session_Status.existing
          val entry =
            Session_Entry(
              chapter = chapter.getOrElse(name, ""),
              groups = groups.getOrElse(name, Nil),
              hostname = hostnames.get(name),
              threads = threads.get(name),
              timing = timing.getOrElse(name, Timing.zero),
              ml_timing = ml_timing.getOrElse(name, Timing.zero),
              sources = sources.get(name),
              heap_size = heap_sizes.get(name),
              status = Some(status),
              errors = errors.getOrElse(name, Nil).reverse,
              theory_timings = theory_timings.getOrElse(name, Map.empty),
              ml_statistics = ml_statistics.getOrElse(name, Nil).reverse)
          (name -> entry)
        }):_*)
    Build_Info(sessions)
  }



  /** session info: produced by isabelle build as session database **/

  sealed case class Session_Info(
    session_timing: Properties.T,
    command_timings: List[Properties.T],
    theory_timings: List[Properties.T],
    ml_statistics: List[Properties.T],
    task_statistics: List[Properties.T],
    errors: List[String]
  ) {
    def error(s: String): Session_Info =
      copy(errors = errors ::: List(s))
  }

  private def parse_session_info(
    log_file: Log_File,
    command_timings: Boolean,
    theory_timings: Boolean,
    ml_statistics: Boolean,
    task_statistics: Boolean
  ): Session_Info = {
    Session_Info(
      session_timing = log_file.find_props(Protocol.Session_Timing_Marker) getOrElse Nil,
      command_timings =
        if (command_timings) log_file.filter_props(Protocol.Command_Timing_Marker) else Nil,
      theory_timings =
        if (theory_timings) log_file.filter_props(Protocol.Theory_Timing_Marker) else Nil,
      ml_statistics =
        if (ml_statistics) log_file.filter_props(Protocol.ML_Statistics_Marker) else Nil,
      task_statistics =
        if (task_statistics) log_file.filter_props(Protocol.Task_Statistics_Marker) else Nil,
      errors = log_file.filter(Protocol.Error_Message_Marker))
  }

  def compress_errors(
    errors: List[String],
    cache: Compress.Cache = Compress.Cache.none
  ): Option[Bytes] =
    if (errors.isEmpty) None
    else {
      Some(Bytes(YXML.string_of_body(XML.Encode.list(XML.Encode.string)(errors))).
        compress(cache = cache))
    }

  def uncompress_errors(bytes: Bytes, cache: XML.Cache = XML.Cache.make()): List[String] =
    if (bytes.is_empty) Nil
    else {
      XML.Decode.list(YXML.string_of_body)(
        YXML.parse_body(bytes.uncompress(cache = cache.compress).text, cache = cache))
    }



  /** persistent store **/

  /* SQL data model */

  object private_data extends SQL.Data("isabelle_build_log") {
    override def tables: SQL.Tables =
      SQL.Tables(
        meta_info_table,
        sessions_table,
        theories_table,
        ml_statistics_table)


    /* main content */

    val log_name = SQL.Column.string("log_name").make_primary_key
    val session_name = SQL.Column.string("session_name").make_primary_key
    val theory_name = SQL.Column.string("theory_name").make_primary_key
    val chapter = SQL.Column.string("chapter")
    val groups = SQL.Column.string("groups")
    val hostname = SQL.Column.string("hostname")
    val threads = SQL.Column.int("threads")
    val timing_elapsed = SQL.Column.long("timing_elapsed")
    val timing_cpu = SQL.Column.long("timing_cpu")
    val timing_gc = SQL.Column.long("timing_gc")
    val timing_factor = SQL.Column.double("timing_factor")
    val ml_timing_elapsed = SQL.Column.long("ml_timing_elapsed")
    val ml_timing_cpu = SQL.Column.long("ml_timing_cpu")
    val ml_timing_gc = SQL.Column.long("ml_timing_gc")
    val ml_timing_factor = SQL.Column.double("ml_timing_factor")
    val theory_timing_elapsed = SQL.Column.long("theory_timing_elapsed")
    val theory_timing_cpu = SQL.Column.long("theory_timing_cpu")
    val theory_timing_gc = SQL.Column.long("theory_timing_gc")
    val heap_size = SQL.Column.long("heap_size")
    val status = SQL.Column.string("status")
    val errors = SQL.Column.bytes("errors")
    val sources = SQL.Column.string("sources")
    val ml_statistics = SQL.Column.bytes("ml_statistics")
    val known = SQL.Column.bool("known")

    val meta_info_table =
      make_table(log_name :: Prop.all_props ::: Settings.all_settings, name = "meta_info")

    val sessions_table =
      make_table(
        List(log_name, session_name, chapter, groups, hostname, threads, timing_elapsed, timing_cpu,
          timing_gc, timing_factor, ml_timing_elapsed, ml_timing_cpu, ml_timing_gc, ml_timing_factor,
          heap_size, status, errors, sources),
        name = "sessions")

    val theories_table =
      make_table(
        List(log_name, session_name, theory_name, theory_timing_elapsed, theory_timing_cpu,
          theory_timing_gc),
        name = "theories")

    val ml_statistics_table =
      make_table(List(log_name, session_name, ml_statistics), name = "ml_statistics")


    /* earliest pull date for repository version (PostgreSQL queries) */

    def pull_date(afp: Boolean = false): SQL.Column =
      if (afp) SQL.Column.date("afp_pull_date")
      else SQL.Column.date("pull_date")

    def pull_date_table(afp: Boolean = false): SQL.Table = {
      val (name, versions) =
        if (afp) ("afp_pull_date", List(Prop.isabelle_version, Prop.afp_version))
        else ("pull_date", List(Prop.isabelle_version))

      make_table(versions.map(_.make_primary_key) ::: List(pull_date(afp)),
        body =
          "SELECT " + versions.mkString(", ") +
            ", min(" + Prop.build_start + ") AS " + pull_date(afp) +
          " FROM " + meta_info_table +
          " WHERE " + SQL.AND((versions ::: List(Prop.build_start)).map(_.defined)) +
          " GROUP BY " + versions.mkString(", "),
        name = name)
    }


    /* recent entries */

    def recent_time(days: Int): PostgreSQL.Source =
      "now() - INTERVAL '" + days.max(0) + " days'"

    def recent_pull_date_table(
      days: Int,
      rev: String = "",
      afp_rev: Option[String] = None
    ): SQL.Table = {
      val afp = afp_rev.isDefined
      val rev2 = afp_rev.getOrElse("")
      val table = pull_date_table(afp)

      val eq_rev = if_proper(rev, Prop.isabelle_version(table).equal(rev))
      val eq_rev2 = if_proper(rev2, Prop.afp_version(table).equal(rev2))

      SQL.Table("recent_pull_date", table.columns,
        table.select(table.columns, sql =
          SQL.where_or(
            pull_date(afp)(table).ident + " > " + recent_time(days),
            SQL.and(eq_rev, eq_rev2))))
    }

    def select_recent_log_names(days: Int): PostgreSQL.Source = {
      val table1 = meta_info_table
      val table2 = recent_pull_date_table(days)
      table1.select(List(log_name), distinct = true, sql =
        SQL.join_inner + table2.query_named +
        " ON " + Prop.isabelle_version(table1) + " = " + Prop.isabelle_version(table2))
    }

    def select_recent_versions(
      days: Int,
      rev: String = "",
      afp_rev: Option[String] = None,
      sql: PostgreSQL.Source = ""
    ): PostgreSQL.Source = {
      val afp = afp_rev.isDefined
      val version = Prop.isabelle_version
      val table1 = recent_pull_date_table(days, rev = rev, afp_rev = afp_rev)
      val table2 = meta_info_table
      val aux_table = SQL.Table("aux", table2.columns, table2.select(sql = sql))

      val columns =
        table1.columns.map(c => c(table1)) :::
          List(known.copy(expr = log_name(aux_table).defined))
      SQL.select(columns, distinct = true) +
        table1.query_named + SQL.join_outer + aux_table.query_named +
        " ON " + version(table1) + " = " + version(aux_table) +
        SQL.order_by(List(pull_date(afp)(table1)), descending = true)
    }


    /* universal view on main data */

    val universal_table: SQL.Table = {
      val afp_pull_date = pull_date(afp = true)
      val version1 = Prop.isabelle_version
      val version2 = Prop.afp_version
      val table1 = meta_info_table
      val table2 = pull_date_table(afp = true)
      val table3 = pull_date_table()

      val a_columns = log_name :: afp_pull_date :: table1.columns.tail
      val a_table =
        SQL.Table("a", a_columns,
          SQL.select(List(log_name, afp_pull_date) ::: table1.columns.tail.map(_.apply(table1))) +
          table1 + SQL.join_outer + table2 + " ON " +
            SQL.and(
              version1(table1).ident + " = " + version1(table2).ident,
              version2(table1).ident + " = " + version2(table2).ident))

      val b_columns = log_name :: pull_date() :: a_columns.tail
      val b_table =
        SQL.Table("b", b_columns,
          SQL.select(
            List(log_name(a_table), pull_date()(table3)) ::: a_columns.tail.map(_.apply(a_table))) +
          a_table.query_named + SQL.join_outer + table3 +
          " ON " + version1(a_table) + " = " + version1(table3))

      val c_columns = b_columns ::: sessions_table.columns.tail
      val c_table =
        SQL.Table("c", c_columns,
          SQL.select(log_name(b_table) :: c_columns.tail) +
          b_table.query_named + SQL.join_inner + sessions_table +
          " ON " + log_name(b_table) + " = " + log_name(sessions_table))

      make_table(c_columns ::: List(ml_statistics),
        body =
          SQL.select(c_columns.map(_.apply(c_table)) ::: List(ml_statistics)) +
          c_table.query_named + SQL.join_outer + ml_statistics_table + " ON " +
            SQL.and(
              log_name(c_table).ident + " = " + log_name(ml_statistics_table).ident,
              session_name(c_table).ident + " = " + session_name(ml_statistics_table).ident))
    }
  }


  /* database access */

  def store(options: Options, cache: XML.Cache = XML.Cache.make()): Store =
    new Store(options, cache)

  class Store private[Build_Log](val options: Options, val cache: XML.Cache) {
    override def toString: String = {
      val s =
        Exn.result { open_database() } match {
          case Exn.Res(db) =>
            val db_name = db.toString
            db.close()
            "database = " + db_name
          case Exn.Exn(_) => "no database"
        }
      "Store(" + s + ")"
    }

    def open_database(server: SSH.Server = SSH.no_server): PostgreSQL.Database =
      PostgreSQL.open_database_server(options, server = server,
        user = options.string("build_log_database_user"),
        password = options.string("build_log_database_password"),
        database = options.string("build_log_database_name"),
        host = options.string("build_log_database_host"),
        port = options.int("build_log_database_port"),
        ssh_host = options.string("build_log_ssh_host"),
        ssh_port = options.int("build_log_ssh_port"),
        ssh_user = options.string("build_log_ssh_user"))

    def init_database(db: SQL.Database, minimal: Boolean = false): Unit =
      private_data.transaction_lock(db, create = true, label = "build_log_init") {
        if (!minimal) {
          db.create_view(private_data.pull_date_table())
          db.create_view(private_data.pull_date_table(afp = true))
        }
        db.create_view(private_data.universal_table)
      }

    def snapshot_database(
      db: PostgreSQL.Database,
      sqlite_database: Path,
      days: Int = 100,
      ml_statistics: Boolean = false
    ): Unit = {
      Isabelle_System.make_directory(sqlite_database.dir)
      sqlite_database.file.delete

      using(SQLite.open_database(sqlite_database)) { db2 =>
        db.transaction {
          db2.transaction {
            // main content
            db2.create_table(private_data.meta_info_table)
            db2.create_table(private_data.sessions_table)
            db2.create_table(private_data.theories_table)
            db2.create_table(private_data.ml_statistics_table)

            val recent_log_names =
              db.execute_query_statement(
                private_data.select_recent_log_names(days),
                List.from[String], res => res.string(private_data.log_name))

            for (log_name <- recent_log_names) {
              read_meta_info(db, log_name).foreach(meta_info =>
                update_meta_info(db2, log_name, meta_info))

              update_sessions(db2, log_name, read_build_info(db, log_name))

              if (ml_statistics) {
                update_ml_statistics(db2, log_name,
                  read_build_info(db, log_name, ml_statistics = true))
              }
            }

            // pull_date
            for (afp <- List(false, true)) {
              val afp_rev = if (afp) Some("") else None
              val table = private_data.pull_date_table(afp)
              db2.create_table(table)
              db2.using_statement(table.insert()) { stmt2 =>
                db.using_statement(
                  private_data.recent_pull_date_table(days, afp_rev = afp_rev).query) { stmt =>
                  using(stmt.execute_query()) { res =>
                    while (res.next()) {
                      for ((c, i) <- table.columns.zipWithIndex) {
                        stmt2.string(i + 1) = res.get_string(c)
                      }
                      stmt2.execute()
                    }
                  }
                }
              }
            }

            // full view
            db2.create_view(private_data.universal_table)
          }
        }
        db2.vacuum()
      }
    }

    def read_domain(
      db: SQL.Database,
      table: SQL.Table,
      column: SQL.Column,
      restriction: Option[Iterable[String]] = None
    ): Set[String] = {
      private_data.transaction_lock(db, label = "Build_Log.read_domain") {
        db.execute_query_statement(
          table.select(List(column),
            sql = restriction match {
              case None => ""
              case Some(names) => column.where_member(names)
            },
            distinct = true),
          Set.from[String], res => cache.string(res.string(column)))
      }
    }

    def update_meta_info(db: SQL.Database, log_name: String, meta_info: Meta_Info): Unit =
      db.execute_statement(db.insert_permissive(private_data.meta_info_table),
        { stmt =>
          stmt.string(1) = log_name
          for ((c, i) <- private_data.meta_info_table.columns.tail.zipWithIndex) {
            if (c.T == SQL.Type.Date) stmt.date(i + 2) = meta_info.get_date(c)
            else stmt.string(i + 2) = meta_info.get(c)
          }
        }
      )

    def update_sessions(db: SQL.Database, log_name: String, build_info: Build_Info): Unit = {
      val sessions =
        if (build_info.sessions.isEmpty) Build_Info.sessions_dummy
        else build_info.sessions
      db.execute_batch_statement(db.insert_permissive(private_data.sessions_table),
        for ((session_name, session) <- sessions) yield { (stmt: SQL.Statement) =>
          stmt.string(1) = log_name
          stmt.string(2) = session_name
          stmt.string(3) = proper_string(session.chapter)
          stmt.string(4) = session.proper_groups
          stmt.string(5) = session.hostname
          stmt.int(6) = session.threads
          stmt.long(7) = session.timing.elapsed.proper_ms
          stmt.long(8) = session.timing.cpu.proper_ms
          stmt.long(9) = session.timing.gc.proper_ms
          stmt.double(10) = session.timing.factor
          stmt.long(11) = session.ml_timing.elapsed.proper_ms
          stmt.long(12) = session.ml_timing.cpu.proper_ms
          stmt.long(13) = session.ml_timing.gc.proper_ms
          stmt.double(14) = session.ml_timing.factor
          stmt.long(15) = session.heap_size.map(_.bytes)
          stmt.string(16) = session.status.map(_.toString)
          stmt.bytes(17) = compress_errors(session.errors, cache = cache.compress)
          stmt.string(18) = session.sources
        }
      )
    }

    def update_theories(db: SQL.Database, log_name: String, build_info: Build_Info): Unit = {
      val sessions =
        if (build_info.sessions.forall({ case (_, session) => session.theory_timings.isEmpty }))
          Build_Info.sessions_dummy
        else build_info.sessions
      db.execute_batch_statement(db.insert_permissive(private_data.theories_table),
        for {
          (session_name, session) <- sessions
          (theory_name, timing) <- session.theory_timings
        } yield { (stmt: SQL.Statement) =>
          stmt.string(1) = log_name
          stmt.string(2) = session_name
          stmt.string(3) = theory_name
          stmt.long(4) = timing.elapsed.ms
          stmt.long(5) = timing.cpu.ms
          stmt.long(6) = timing.gc.ms
        }
      )
    }

    def update_ml_statistics(db: SQL.Database, log_name: String, build_info: Build_Info): Unit = {
      val ml_stats: List[(String, Option[Bytes])] =
        Par_List.map[(String, Session_Entry), (String, Option[Bytes])](
          { case (a, b) => (a, Properties.compress(b.ml_statistics, cache = cache.compress).proper) },
          build_info.sessions.iterator.filter(p => p._2.ml_statistics.nonEmpty).toList)
      val entries = if (ml_stats.nonEmpty) ml_stats else List("" -> None)
      db.execute_batch_statement(db.insert_permissive(private_data.ml_statistics_table),
        for ((session_name, ml_statistics) <- entries) yield { (stmt: SQL.Statement) =>
          stmt.string(1) = log_name
          stmt.string(2) = session_name
          stmt.bytes(3) = ml_statistics
        }
      )
    }

    def write_info(db: SQL.Database, files: List[JFile],
      ml_statistics: Boolean = false,
      progress: Progress = new Progress,
      errors: Multi_Map[String, String] = Multi_Map.empty
    ): Multi_Map[String, String] = {
      init_database(db)

      val errors_result = Synchronized(errors)
      def add_error(name: String, exn: Throwable): Unit =
        errors_result.change(_.insert(name, Exn.print(exn)))

      val files_domain = {
        val names = files.map(Log_File.plain_name).toSet
        if (names.size > 100) None else Some(names)
      }

      abstract class Table_Status(table: SQL.Table) {
        private val known =
          Synchronized(read_domain(db, table, private_data.log_name, restriction = files_domain))

        def required(file: JFile): Boolean = !(known.value)(Log_File.plain_name(file))
        def required(log_file: Log_File): Boolean = !(known.value)(log_file.name)

        def update_db(db: SQL.Database, log_file: Log_File): Unit
        def update(log_file: Log_File): Unit = {
          if (required(log_file)) {
            update_db(db, log_file)
            known.change(_ + log_file.name)
          }
        }
      }

      val ml_statistics_status =
        if (ml_statistics) Nil
        else {
          List(
            new Table_Status(private_data.ml_statistics_table) {
              override def update_db(db: SQL.Database, log_file: Log_File): Unit =
                update_ml_statistics(db, log_file.name,
                  log_file.parse_build_info(ml_statistics = true))
            })
        }
      val status =
        List(
          new Table_Status(private_data.meta_info_table) {
            override def update_db(db: SQL.Database, log_file: Log_File): Unit =
              update_meta_info(db, log_file.name, log_file.parse_meta_info())
          },
          new Table_Status(private_data.sessions_table) {
            override def update_db(db: SQL.Database, log_file: Log_File): Unit =
              update_sessions(db, log_file.name, log_file.parse_build_info())
          },
          new Table_Status(private_data.theories_table) {
            override def update_db(db: SQL.Database, log_file: Log_File): Unit =
              update_theories(db, log_file.name, log_file.parse_build_info())
          }
        ) ::: ml_statistics_status

      val consumer =
        Consumer_Thread.fork[Log_File]("build_log_database")(
          consume = { log_file =>
            private_data.transaction_lock(db, label = "build_log_database") {
              try { status.foreach(_.update(log_file)) }
              catch { case exn: Throwable => add_error(log_file.name, exn) }
            }
            true
          },
          limit = 1
        )

      try {
        for (file <- files.iterator if status.exists(_.required(file))) {
          val log_name = Log_File.plain_name(file)
          progress.echo("Log " + quote(log_name), verbose = true)
          Exn.result { Log_File(file) } match {
            case Exn.Res(log_file) => consumer.send(log_file)
            case Exn.Exn(exn) => add_error(log_name, exn)
          }
        }
      }
      finally { consumer.shutdown() }

      errors_result.value
    }

    def read_meta_info(db: SQL.Database, log_name: String): Option[Meta_Info] = {
      val table = private_data.meta_info_table
      val columns = table.columns.tail
      db.execute_query_statementO[Meta_Info](
        table.select(columns, sql = private_data.log_name.where_equal(log_name)),
        { res =>
          val results =
            columns.map(c => c.name ->
              (if (c.T == SQL.Type.Date)
                res.get_date(c).map(Log_File.Date_Format(_))
               else
                res.get_string(c)))
          val n = Prop.all_props.length
          val props = for (case (x, Some(y)) <- results.take(n)) yield (x, y)
          val settings = for (case (x, Some(y)) <- results.drop(n)) yield (x, y)
          Meta_Info(props, settings)
        }
      )
    }

    def read_build_info(
      db: SQL.Database,
      log_name: String,
      session_names: List[String] = Nil,
      ml_statistics: Boolean = false
    ): Build_Info = {
      val table1 = private_data.sessions_table
      val table2 = private_data.ml_statistics_table

      val columns1 = table1.columns.tail.map(_.apply(table1))
      val (columns, from) =
        if (ml_statistics) {
          val columns = columns1 ::: List(private_data.ml_statistics(table2))
          val join =
            table1.ident + SQL.join_outer + table2.ident + " ON " +
              SQL.and(
                private_data.log_name(table1).ident + " = " + private_data.log_name(table2).ident,
                private_data.session_name(table1).ident + " = " + private_data.session_name(table2).ident)
          (columns, SQL.enclose(join))
        }
        else (columns1, table1.ident)

      val where =
        SQL.where_and(
          private_data.log_name(table1).equal(log_name),
          private_data.session_name(table1).ident + " <> ''",
          if_proper(session_names, private_data.session_name(table1).member(session_names)))

      val sessions =
        db.execute_query_statement(
          SQL.select(columns, sql = from + where),
          Map.from[String, Session_Entry],
          { res =>
            val session_name = res.string(private_data.session_name)
            val session_entry =
              Session_Entry(
                chapter = res.string(private_data.chapter),
                groups = split_lines(res.string(private_data.groups)),
                hostname = res.get_string(private_data.hostname),
                threads = res.get_int(private_data.threads),
                timing =
                  res.timing(
                    private_data.timing_elapsed,
                    private_data.timing_cpu,
                    private_data.timing_gc),
                ml_timing =
                  res.timing(
                    private_data.ml_timing_elapsed,
                    private_data.ml_timing_cpu,
                    private_data.ml_timing_gc),
                sources = res.get_string(private_data.sources),
                heap_size = res.get_long(private_data.heap_size).map(Space.bytes),
                status = res.get_string(private_data.status).map(Session_Status.valueOf),
                errors = uncompress_errors(res.bytes(private_data.errors), cache = cache),
                ml_statistics =
                  if (ml_statistics) {
                    Properties.uncompress(res.bytes(private_data.ml_statistics), cache = cache)
                  }
                  else Nil)
            session_name -> session_entry
          }
        )
      Build_Info(sessions)
    }
  }


  /** maintain build_log database **/

  def build_log_database(options: Options, logs: List[Path],
    progress: Progress = new Progress,
    vacuum: Boolean = false,
    ml_statistics: Boolean = false,
    snapshot: Option[Path] = None
  ): Unit = {
    val store = Build_Log.store(options)

    val log_files = Log_File.find_files(logs.map(_.file))

    using(store.open_database()) { db =>
      if (vacuum) db.vacuum()

      progress.echo("Updating database " + db + " ...")
      val errors0 = store.write_info(db, log_files, progress = progress)

      val errors =
        if (ml_statistics) {
          progress.echo("Updating database " + db + " (ML statistics) ...")
          store.write_info(db, log_files, ml_statistics = true, errors = errors0)
        }
        else errors0

      if (errors.isEmpty) {
        for (path <- snapshot) {
          progress.echo("Writing database snapshot " + path)
          store.snapshot_database(db, path)
        }
      }
      else {
        error(cat_lines(List.from(
          for ((name, rev_errs) <- errors.iterator_list) yield {
            val err = "The error(s) above occurred in " + quote(name)
            cat_lines((err :: rev_errs).reverse)
          }
        )))
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("build_log_database", "update build_log database from log files",
    Scala_Project.here,
    { args =>
      var ml_statistics: Boolean = false
      var snapshot: Option[Path] = None
      var vacuum = false
      var logs: List[Path] = Nil
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle build_log_database [OPTIONS]

  Options are:
    -M           include ML statistics
    -S FILE      snapshot to SQLite db file
    -V           vacuum cleaning of database
    -d LOG       include log file start location
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose

  Update the build_log database server from log files, which are recursively
  collected from given start locations (files or directories).
""",
        "M" -> (_ => ml_statistics = true),
        "S:" -> (arg => snapshot = Some(Path.explode(arg))),
        "V" -> (_ => vacuum = true),
        "d:" -> (arg => logs = logs ::: List(Path.explode(arg))),
        "o:" -> (arg => options = options + arg),
        "v" -> (_ => verbose = true))

      val more_args = getopts(args)
      if (more_args.nonEmpty) getopts.usage()

      val progress = new Console_Progress(verbose = verbose)

      build_log_database(options, logs, progress = progress, vacuum = vacuum,
        ml_statistics = ml_statistics, snapshot = snapshot)
    })
}

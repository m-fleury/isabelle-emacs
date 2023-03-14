/*  Title:      Pure/Tools/build_job.scala
    Author:     Makarius

Build job running prover process, with rudimentary PIDE session.
*/

package isabelle


import scala.collection.mutable


trait Build_Job {
  def cancel(): Unit = ()
  def is_finished: Boolean = false
  def join: (Process_Result, SHA1.Shasum) = (Process_Result.undefined, SHA1.no_shasum)
}

object Build_Job {
  /* build session */

  def start_session(
    build_context: Build_Process.Context,
    progress: Progress,
    log: Logger,
    session_background: Sessions.Background,
    input_shasum: SHA1.Shasum,
    node_info: Host.Node_Info
  ): Session_Job = {
    new Session_Job(build_context, progress, log, session_background, input_shasum, node_info)
  }

  object Session_Context {
    def load(
      build_uuid: String,
      name: String,
      deps: List[String],
      ancestors: List[String],
      session_prefs: String,
      sources_shasum: SHA1.Shasum,
      timeout: Time,
      store: Sessions.Store,
      progress: Progress = new Progress
    ): Session_Context = {
      def default: Session_Context =
        Session_Context(
          name, deps, ancestors, session_prefs, sources_shasum, timeout,
          Time.zero, Bytes.empty, build_uuid)

      store.try_open_database(name) match {
        case None => default
        case Some(db) =>
          def ignore_error(msg: String) = {
            progress.echo_warning(
              "Ignoring bad database " + db + " for session " + quote(name) +
              if_proper(msg, ":\n" + msg))
            default
          }
          try {
            val command_timings = store.read_command_timings(db, name)
            val elapsed =
              store.read_session_timing(db, name) match {
                case Markup.Elapsed(s) => Time.seconds(s)
                case _ => Time.zero
              }
            new Session_Context(
              name, deps, ancestors, session_prefs, sources_shasum, timeout,
              elapsed, command_timings, build_uuid)
          }
          catch {
            case ERROR(msg) => ignore_error(msg)
            case exn: java.lang.Error => ignore_error(Exn.message(exn))
            case _: XML.Error => ignore_error("XML.Error")
          }
          finally { db.close() }
      }
    }
  }

  sealed case class Session_Context(
    name: String,
    deps: List[String],
    ancestors: List[String],
    session_prefs: String,
    sources_shasum: SHA1.Shasum,
    timeout: Time,
    old_time: Time,
    old_command_timings_blob: Bytes,
    build_uuid: String
  ) extends Library.Named

  class Session_Job private[Build_Job](
    build_context: Build_Process.Context,
    progress: Progress,
    log: Logger,
    session_background: Sessions.Background,
    input_shasum: SHA1.Shasum,
    node_info: Host.Node_Info
  ) extends Build_Job {
    private val store = build_context.store

    def session_name: String = session_background.session_name

    private val info: Sessions.Info = session_background.sessions_structure(session_name)
    private val options: Options = node_info.process_policy(info.options)

    private val session_sources =
      Sessions.Sources.load(session_background.base, cache = store.cache.compress)

    private val store_heap = build_context.store_heap(session_name)

    private val future_result: Future[(Process_Result, SHA1.Shasum)] =
      Future.thread("build", uninterruptible = true) {
        val env =
          Isabelle_System.settings(
            List("ISABELLE_ML_DEBUGGER" -> options.bool("ML_debugger").toString))

        val session_heaps =
          session_background.info.parent match {
            case None => Nil
            case Some(logic) => ML_Process.session_heaps(store, session_background, logic = logic)
          }

        val use_prelude = if (session_heaps.isEmpty) Thy_Header.ml_roots.map(_._1) else Nil

        val eval_store =
          if (store_heap) {
            (if (info.theories.nonEmpty) List("ML_Heap.share_common_data ()") else Nil) :::
            List("ML_Heap.save_child " +
              ML_Syntax.print_string_bytes(File.platform_path(store.output_heap(session_name))))
          }
          else Nil

        def session_blobs(node_name: Document.Node.Name): List[(Command.Blob, Document.Blobs.Item)] =
          session_background.base.theory_load_commands.get(node_name.theory) match {
            case None => Nil
            case Some(spans) =>
              val syntax = session_background.base.theory_syntax(node_name)
              val master_dir = Path.explode(node_name.master_dir)
              for (span <- spans; file <- span.loaded_files(syntax).files)
                yield {
                  val src_path = Path.explode(file)
                  val blob_name = Document.Node.Name(File.symbolic_path(master_dir + src_path))

                  val bytes = session_sources(blob_name.node).bytes
                  val text = bytes.text
                  val chunk = Symbol.Text_Chunk(text)

                  Command.Blob(blob_name, src_path, Some((SHA1.digest(bytes), chunk))) ->
                    Document.Blobs.Item(bytes, text, chunk, changed = false)
                }
          }


        /* session */

        val resources =
          new Resources(session_background, log = log,
            command_timings = build_context.old_command_timings(session_name))

        val session =
          new Session(options, resources) {
            override val cache: Term.Cache = store.cache

            override def build_blobs_info(node_name: Document.Node.Name): Command.Blobs_Info =
              Command.Blobs_Info.make(session_blobs(node_name))

            override def build_blobs(node_name: Document.Node.Name): Document.Blobs =
              Document.Blobs.make(session_blobs(node_name))
          }

        object Build_Session_Errors {
          private val promise: Promise[List[String]] = Future.promise

          def result: Exn.Result[List[String]] = promise.join_result
          def cancel(): Unit = promise.cancel()
          def apply(errs: List[String]): Unit = {
            try { promise.fulfill(errs) }
            catch { case _: IllegalStateException => }
          }
        }

        val export_consumer =
          Export.consumer(store.open_database(session_name, output = true), store.cache,
            progress = progress)

        val stdout = new StringBuilder(1000)
        val stderr = new StringBuilder(1000)
        val command_timings = new mutable.ListBuffer[Properties.T]
        val theory_timings = new mutable.ListBuffer[Properties.T]
        val session_timings = new mutable.ListBuffer[Properties.T]
        val runtime_statistics = new mutable.ListBuffer[Properties.T]
        val task_statistics = new mutable.ListBuffer[Properties.T]

        def fun(
          name: String,
          acc: mutable.ListBuffer[Properties.T],
          unapply: Properties.T => Option[Properties.T]
        ): (String, Session.Protocol_Function) = {
          name -> ((msg: Prover.Protocol_Output) =>
            unapply(msg.properties) match {
              case Some(props) => acc += props; true
              case _ => false
            })
        }

        session.init_protocol_handler(new Session.Protocol_Handler {
            override def exit(): Unit = Build_Session_Errors.cancel()

            private def build_session_finished(msg: Prover.Protocol_Output): Boolean = {
              val (rc, errors) =
                try {
                  val (rc, errs) = {
                    import XML.Decode._
                    pair(int, list(x => x))(Symbol.decode_yxml(msg.text))
                  }
                  val errors =
                    for (err <- errs) yield {
                      val prt = Protocol_Message.expose_no_reports(err)
                      Pretty.string_of(prt, metric = Symbol.Metric)
                    }
                  (rc, errors)
                }
                catch { case ERROR(err) => (Process_Result.RC.failure, List(err)) }

              session.protocol_command("Prover.stop", rc.toString)
              Build_Session_Errors(errors)
              true
            }

            private def loading_theory(msg: Prover.Protocol_Output): Boolean =
              msg.properties match {
                case Markup.Loading_Theory(Markup.Name(name)) =>
                  progress.theory(Progress.Theory(name, session = session_name))
                  false
                case _ => false
              }

            private def export_(msg: Prover.Protocol_Output): Boolean =
              msg.properties match {
                case Protocol.Export(args) =>
                  export_consumer.make_entry(session_name, args, msg.chunk)
                  true
                case _ => false
              }

            override val functions: Session.Protocol_Functions =
              List(
                Markup.Build_Session_Finished.name -> build_session_finished,
                Markup.Loading_Theory.name -> loading_theory,
                Markup.EXPORT -> export_,
                fun(Markup.Theory_Timing.name, theory_timings, Markup.Theory_Timing.unapply),
                fun(Markup.Session_Timing.name, session_timings, Markup.Session_Timing.unapply),
                fun(Markup.Task_Statistics.name, task_statistics, Markup.Task_Statistics.unapply))
          })

        session.command_timings += Session.Consumer("command_timings") {
          case Session.Command_Timing(props) =>
            for {
              elapsed <- Markup.Elapsed.unapply(props)
              elapsed_time = Time.seconds(elapsed)
              if elapsed_time.is_relevant && elapsed_time >= options.seconds("command_timing_threshold")
            } command_timings += props.filter(Markup.command_timing_property)
        }

        session.runtime_statistics += Session.Consumer("ML_statistics") {
          case Session.Runtime_Statistics(props) => runtime_statistics += props
        }

        session.finished_theories += Session.Consumer[Document.Snapshot]("finished_theories") {
          case snapshot =>
            if (!progress.stopped) {
              def export_(name: String, xml: XML.Body, compress: Boolean = true): Unit = {
                if (!progress.stopped) {
                  val theory_name = snapshot.node_name.theory
                  val args =
                    Protocol.Export.Args(theory_name = theory_name, name = name, compress = compress)
                  val body = Bytes(Symbol.encode(YXML.string_of_body(xml)))
                  export_consumer.make_entry(session_name, args, body)
                }
              }
              def export_text(name: String, text: String, compress: Boolean = true): Unit =
                export_(name, List(XML.Text(text)), compress = compress)

              for (command <- snapshot.snippet_command) {
                export_text(Export.DOCUMENT_ID, command.id.toString, compress = false)
              }

              export_text(Export.FILES,
                cat_lines(snapshot.node_files.map(name => File.symbolic_path(name.path))),
                compress = false)

              for ((blob_name, i) <- snapshot.node_files.tail.zipWithIndex) {
                val xml = snapshot.switch(blob_name).xml_markup()
                export_(Export.MARKUP + (i + 1), xml)
              }
              export_(Export.MARKUP, snapshot.xml_markup())
              export_(Export.MESSAGES, snapshot.messages.map(_._1))
            }
        }

        session.all_messages += Session.Consumer[Any]("build_session_output") {
          case msg: Prover.Output =>
            val message = msg.message
            if (msg.is_system) resources.log(Protocol.message_text(message))

            if (msg.is_stdout) {
              stdout ++= Symbol.encode(XML.content(message))
            }
            else if (msg.is_stderr) {
              stderr ++= Symbol.encode(XML.content(message))
            }
            else if (msg.is_exit) {
              val err =
                "Prover terminated" +
                  (msg.properties match {
                    case Markup.Process_Result(result) => ": " + result.print_rc
                    case _ => ""
                  })
              Build_Session_Errors(List(err))
            }
          case _ =>
        }

        build_context.session_setup(session_name, session)

        val eval_main = Command_Line.ML_tool("Isabelle_Process.init_build ()" :: eval_store)


        /* process */

        val process =
          Isabelle_Process.start(options, session, session_background, session_heaps,
            use_prelude = use_prelude, eval_main = eval_main, cwd = info.dir.file, env = env)

        val timeout_request: Option[Event_Timer.Request] =
          if (info.timeout_ignored) None
          else Some(Event_Timer.request(Time.now() + info.timeout) { process.terminate() })

        val build_errors =
          Isabelle_Thread.interrupt_handler(_ => process.terminate()) {
            Exn.capture { process.await_startup() } match {
              case Exn.Res(_) =>
                val resources_yxml = resources.init_session_yxml
                val encode_options: XML.Encode.T[Options] =
                  options => session.prover_options(options).encode
                val args_yxml =
                  YXML.string_of_body(
                    {
                      import XML.Encode._
                      pair(string, list(pair(encode_options, list(pair(string, properties)))))(
                        (session_name, info.theories))
                    })
                session.protocol_command("build_session", resources_yxml, args_yxml)
                Build_Session_Errors.result
              case Exn.Exn(exn) => Exn.Res(List(Exn.message(exn)))
            }
          }

        val result0 =
          Isabelle_Thread.interrupt_handler(_ => process.terminate()) { process.await_shutdown() }

        val was_timeout =
          timeout_request match {
            case None => false
            case Some(request) => !request.cancel()
          }

        session.stop()

        val export_errors =
          export_consumer.shutdown(close = true).map(Output.error_message_text)

        val (document_output, document_errors) =
          try {
            if (build_errors.isInstanceOf[Exn.Res[_]] && result0.ok && info.documents.nonEmpty) {
              using(Export.open_database_context(store)) { database_context =>
                val documents =
                  using(database_context.open_session(session_background)) {
                    session_context =>
                      Document_Build.build_documents(
                        Document_Build.context(session_context, progress = progress),
                        output_sources = info.document_output,
                        output_pdf = info.document_output)
                  }
                using(database_context.open_database(session_name, output = true))(session_database =>
                  documents.foreach(_.write(session_database.db, session_name)))
                (documents.flatMap(_.log_lines), Nil)
              }
            }
            else (Nil, Nil)
          }
          catch {
            case exn: Document_Build.Build_Error => (exn.log_lines, exn.log_errors)
            case Exn.Interrupt.ERROR(msg) => (Nil, List(msg))
          }


        /* process result */

        val result1 = {
          val theory_timing =
            theory_timings.iterator.flatMap(
              {
                case props @ Markup.Name(name) => Some(name -> props)
                case _ => None
              }).toMap
          val used_theory_timings =
            for { (name, _) <- session_background.base.used_theories }
              yield theory_timing.getOrElse(name.theory, Markup.Name(name.theory))

          val more_output =
            Library.trim_line(stdout.toString) ::
              command_timings.toList.map(Protocol.Command_Timing_Marker.apply) :::
              used_theory_timings.map(Protocol.Theory_Timing_Marker.apply) :::
              session_timings.toList.map(Protocol.Session_Timing_Marker.apply) :::
              runtime_statistics.toList.map(Protocol.ML_Statistics_Marker.apply) :::
              task_statistics.toList.map(Protocol.Task_Statistics_Marker.apply) :::
              document_output

          result0.output(more_output)
            .error(Library.trim_line(stderr.toString))
            .errors_rc(export_errors ::: document_errors)
        }

        val result2 =
          build_errors match {
            case Exn.Res(build_errs) =>
              val errs = build_errs ::: document_errors
              if (errs.nonEmpty) {
                result1.error_rc.output(
                  errs.flatMap(s => split_lines(Output.error_message_text(s))) :::
                    errs.map(Protocol.Error_Message_Marker.apply))
              }
              else if (progress.stopped && result1.ok) result1.copy(rc = Process_Result.RC.interrupt)
              else result1
            case Exn.Exn(Exn.Interrupt()) =>
              if (result1.ok) result1.copy(rc = Process_Result.RC.interrupt)
              else result1
            case Exn.Exn(exn) => throw exn
          }

        val process_result =
          if (result2.ok) result2
          else if (was_timeout) result2.error(Output.error_message_text("Timeout")).timeout_rc
          else if (result2.interrupted) result2.error(Output.error_message_text("Interrupt"))
          else result2


        /* output heap */

        val output_shasum =
          if (process_result.ok && store_heap && store.output_heap(session_name).is_file) {
            SHA1.shasum(ML_Heap.write_digest(store.output_heap(session_name)), session_name)
          }
          else SHA1.no_shasum

        val log_lines = process_result.out_lines.filterNot(Protocol_Message.Marker.test)

        val build_log =
          Build_Log.Log_File(session_name, process_result.out_lines).
            parse_session_info(
              command_timings = true,
              theory_timings = true,
              ml_statistics = true,
              task_statistics = true)

        // write log file
        if (process_result.ok) {
          File.write_gzip(store.output_log_gz(session_name), terminate_lines(log_lines))
        }
        else File.write(store.output_log(session_name), terminate_lines(log_lines))

        // write database
        using(store.open_database(session_name, output = true))(db =>
          store.write_session_info(db, session_name, session_sources,
            build_log =
              if (process_result.timeout) build_log.error("Timeout") else build_log,
            build =
              Sessions.Build_Info(
                sources = build_context.sources_shasum(session_name),
                input_heaps = input_shasum,
                output_heap = output_shasum,
                process_result.rc,
                build_context.build_uuid)))

        // messages
        process_result.err_lines.foreach(progress.echo(_))

        if (process_result.ok) {
          val props = build_log.session_timing
          val threads = Markup.Session_Timing.Threads.unapply(props) getOrElse 1
          val timing = Markup.Timing_Properties.get(props)
          progress.echo(
            "Timing " + session_name + " (" + threads + " threads, " + timing.message_factor + ")",
            verbose = true)
          progress.echo(
            "Finished " + session_name + " (" + process_result.timing.message_resources + ")")
        }
        else {
          progress.echo(
            session_name + " FAILED (see also \"isabelle build_log -H Error " + session_name + "\")")
          if (!process_result.interrupted) {
            val tail = info.options.int("process_output_tail")
            val suffix = if (tail == 0) log_lines else log_lines.drop(log_lines.length - tail max 0)
            val prefix = if (log_lines.length == suffix.length) Nil else List("...")
            progress.echo(Library.trim_line(cat_lines(prefix ::: suffix)))
          }
        }

        (process_result.copy(out_lines = log_lines), output_shasum)
      }

    override def cancel(): Unit = future_result.cancel()
    override def is_finished: Boolean = future_result.is_finished
    override def join: (Process_Result, SHA1.Shasum) = future_result.join
  }


  /* theory markup/messages from session database */

  def read_theory(
    theory_context: Export.Theory_Context,
    unicode_symbols: Boolean = false
  ): Option[Document.Snapshot] = {
    def decode_bytes(bytes: Bytes): String =
      Symbol.output(unicode_symbols, UTF8.decode_permissive(bytes))

    def read(name: String): Export.Entry = theory_context(name, permissive = true)

    def read_xml(name: String): XML.Body =
      YXML.parse_body(decode_bytes(read(name).bytes), cache = theory_context.cache)

    def read_source_file(name: String): Sessions.Source_File =
      theory_context.session_context.source_file(name)

    for {
      id <- theory_context.document_id()
      (thy_file, blobs_files) <- theory_context.files(permissive = true)
    }
    yield {
      val master_dir =
        Path.explode(Url.strip_base_name(thy_file).getOrElse(
          error("Cannot determine theory master directory: " + quote(thy_file))))

      val blobs =
        blobs_files.map { name =>
          val path = Path.explode(name)
          val src_path = File.relative_path(master_dir, path).getOrElse(path)

          val file = read_source_file(name)
          val bytes = file.bytes
          val text = decode_bytes(bytes)
          val chunk = Symbol.Text_Chunk(text)

          Command.Blob(Document.Node.Name(name), src_path, Some((file.digest, chunk))) ->
            Document.Blobs.Item(bytes, text, chunk, changed = false)
        }

      val thy_source = decode_bytes(read_source_file(thy_file).bytes)
      val thy_xml = read_xml(Export.MARKUP)
      val blobs_xml =
        for (i <- (1 to blobs.length).toList)
          yield read_xml(Export.MARKUP + i)

      val markups_index = Command.Markup_Index.make(blobs.map(_._1))
      val markups =
        Command.Markups.make(
          for ((index, xml) <- markups_index.zip(thy_xml :: blobs_xml))
          yield index -> Markup_Tree.from_XML(xml))

      val results =
        Command.Results.make(
          for (elem @ XML.Elem(Markup(_, Markup.Serial(i)), _) <- read_xml(Export.MESSAGES))
            yield i -> elem)

      val command =
        Command.unparsed(thy_source, theory = true, id = id,
          node_name = Document.Node.Name(thy_file, theory = theory_context.theory),
          blobs_info = Command.Blobs_Info.make(blobs),
          markups = markups, results = results)

      val doc_blobs = Document.Blobs.make(blobs)

      Document.State.init.snippet(command, doc_blobs)
    }
  }
}

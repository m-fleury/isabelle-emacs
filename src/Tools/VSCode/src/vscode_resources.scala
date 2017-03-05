/*  Title:      Tools/VSCode/src/vscode_resources.scala
    Author:     Makarius

Resources for VSCode Language Server: file-system access and global state.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.util.parsing.input.Reader


object VSCode_Resources
{
  /* internal state */

  sealed case class State(
    models: Map[JFile, Document_Model] = Map.empty,
    pending_input: Set[JFile] = Set.empty,
    pending_output: Set[JFile] = Set.empty)
  {
    def pending(changed: Traversable[JFile]) =
      copy(
        pending_input = pending_input ++ changed,
        pending_output = pending_output ++ changed)

    lazy val document_blobs: Document.Blobs =
      Document.Blobs(
        (for {
          (_, model) <- models.iterator
          blob <- model.get_blob
        } yield (model.node_name -> blob)).toMap)
  }
}

class VSCode_Resources(
  val options: Options,
  val text_length: Text.Length,
  base: Sessions.Base,
  log: Logger = No_Logger) extends Resources(base, log)
{
  private val state = Synchronized(VSCode_Resources.State())


  /* document node name */

  def node_file(name: Document.Node.Name): JFile = new JFile(name.node)

  def node_name(file: JFile): Document.Node.Name =
  {
    val node = file.getPath
    val theory = Thy_Header.thy_name_bootstrap(node).getOrElse("")
    val master_dir = if (theory == "") "" else file.getParent
    Document.Node.Name(node, master_dir, theory)
  }

  override def append(dir: String, source_path: Path): String =
  {
    val path = source_path.expand
    if (dir == "" || path.is_absolute) File.platform_path(path)
    else if (path.is_current) dir
    else if (path.is_basic && !dir.endsWith("/") && !dir.endsWith(JFile.separator))
      dir + JFile.separator + File.platform_path(path)
    else if (path.is_basic) dir + File.platform_path(path)
    else new JFile(dir + JFile.separator + File.platform_path(path)).getCanonicalPath
  }

  def get_model(file: JFile): Option[Document_Model] = state.value.models.get(file)
  def get_model(name: Document.Node.Name): Option[Document_Model] = get_model(node_file(name))


  /* file content */

  def read_file_content(file: JFile): Option[String] =
    try { Some(Line.normalize(File.read(file))) }
    catch { case ERROR(_) => None }

  def get_file_content(file: JFile): Option[String] =
    get_model(file) match {
      case Some(model) => Some(model.content.text)
      case None => read_file_content(file)
    }

  def bibtex_entries_iterator(): Iterator[Text.Info[(String, Document_Model)]] =
    for {
      (_, model) <- state.value.models.iterator
      Text.Info(range, entry) <- model.content.bibtex_entries.iterator
    } yield Text.Info(range, (entry, model))

  override def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A =
  {
    val file = node_file(name)
    get_model(file) match {
      case Some(model) => f(Scan.char_reader(model.content.text))
      case None if file.isFile =>
        val reader = Scan.byte_reader(file)
        try { f(reader) } finally { reader.close }
      case None =>
        error("No such file: " + quote(file.toString))
    }
  }


  /* document models */

  def visible_node(name: Document.Node.Name): Boolean =
    get_model(name) match {
      case Some(model) => model.node_visible
      case None => false
    }

  def update_model(session: Session, file: JFile, text: String)
  {
    state.change(st =>
      {
        val model = st.models.getOrElse(file, Document_Model.init(session, node_name(file)))
        val model1 = (model.update_text(text) getOrElse model).external(false)
        st.copy(
          models = st.models + (file -> model1),
          pending_input = st.pending_input + file,
          pending_output = st.pending_output ++
            (if (model.node_visible == model1.node_visible) None else Some(file)))
      })
  }

  def close_model(file: JFile): Boolean =
    state.change_result(st =>
      st.models.get(file) match {
        case None => (false, st)
        case Some(model) =>
          val model1 = model.external(true)
          (true, st.copy(models = st.models + (file -> model1)).pending(Some(file)))
      })

  def sync_models(changed_files: Set[JFile]): Boolean =
    state.change_result(st =>
      {
        val changed_models =
          (for {
            (file, model) <- st.models.iterator
            if changed_files(file) && model.external_file
            text <- read_file_content(file)
            model1 <- model.update_text(text)
          } yield (file, model1)).toMap
        if (changed_models.isEmpty) (false, st)
        else (true, st.copy(models = st.models ++ changed_models).pending(changed_models.keySet))
      })


  /* resolve dependencies */

  def resolve_dependencies(session: Session, file_watcher: File_Watcher): (Boolean, Boolean) =
  {
    state.change_result(st =>
      {
        /* theory files */

        val thys =
          (for ((_, model) <- st.models.iterator if model.is_theory)
           yield (model.node_name, Position.none)).toList

        val thy_files = thy_info.dependencies("", thys).deps.map(_.name)


        /* auxiliary files */

        val stable_tip_version =
          if (st.models.forall(entry => entry._2.is_stable))
            session.current_state().stable_tip_version
          else None

        val aux_files =
          stable_tip_version match {
            case Some(version) => undefined_blobs(version.nodes)
            case None => Nil
          }


        /* loaded models */

        val loaded_models =
          (for {
            node_name <- thy_files.iterator ++ aux_files.iterator
            file = node_file(node_name)
            if !st.models.isDefinedAt(file)
            text <- { file_watcher.register_parent(file); read_file_content(file) }
          }
          yield {
            val model = Document_Model.init(session, node_name)
            val model1 = (model.update_text(text) getOrElse model).external(true)
            (file, model1)
          }).toMap

        val invoke_input = loaded_models.nonEmpty
        val invoke_load = stable_tip_version.isEmpty

        ((invoke_input, invoke_load),
          st.copy(models = st.models ++ loaded_models).pending(loaded_models.keySet))
      })
  }


  /* pending input */

  def flush_input(session: Session)
  {
    state.change(st =>
      {
        val changed_models =
          (for {
            file <- st.pending_input.iterator
            model <- st.models.get(file)
            (edits, model1) <- model.flush_edits(st.document_blobs)
          } yield (edits, (file, model1))).toList

        session.update(st.document_blobs, changed_models.flatMap(_._1))
        st.copy(
          models = st.models ++ changed_models.iterator.map(_._2),
          pending_input = Set.empty)
      })
  }


  /* pending output */

  def update_output(changed_nodes: List[JFile]): Unit =
    state.change(st => st.copy(pending_output = st.pending_output ++ changed_nodes))

  def flush_output(channel: Channel)
  {
    state.change(st =>
      {
        val changed_iterator =
          for {
            file <- st.pending_output.iterator
            model <- st.models.get(file)
            rendering = model.rendering()
            ((diagnostics, decorations), model1) <- model.publish(rendering)
          }
          yield {
            if (diagnostics.nonEmpty)
              channel.write(
                Protocol.PublishDiagnostics(file, rendering.diagnostics_output(diagnostics)))

            for (decoration <- decorations)
              channel.write(rendering.decoration_output(decoration).json(file))

            (file, model1)
          }
        st.copy(
          models = st.models ++ changed_iterator,
          pending_output = Set.empty)
      }
    )
  }


  /* output text */

  def decode_text: Boolean = options.bool("vscode_unicode_symbols")
  def tooltip_margin: Int = options.int("vscode_tooltip_margin")
  def message_margin: Int = options.int("vscode_message_margin")

  def output_text(s: String): String =
    if (decode_text) Symbol.decode(s) else Symbol.encode(s)

  def output_xml(xml: XML.Tree): String =
    output_text(XML.content(xml))

  def output_pretty(body: XML.Body, margin: Int): String =
    output_text(Pretty.string_of(body, margin))
  def output_pretty_tooltip(body: XML.Body): String = output_pretty(body, tooltip_margin)
  def output_pretty_message(body: XML.Body): String = output_pretty(body, message_margin)
}

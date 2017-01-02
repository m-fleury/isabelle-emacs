/*  Title:      Tools/VSCode/src/vscode_resources.scala
    Author:     Makarius

Resources for VSCode Language Server: file-system access and global state.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.util.parsing.input.{Reader, CharSequenceReader}


object VSCode_Resources
{
  /* internal state */

  sealed case class State(
    models: Map[String, Document_Model] = Map.empty,
    pending_input: Set[String] = Set.empty,
    pending_output: Set[String] = Set.empty)
}

class VSCode_Resources(
    val options: Options,
    val text_length: Text.Length,
    loaded_theories: Set[String],
    known_theories: Map[String, Document.Node.Name],
    base_syntax: Outer_Syntax,
    log: Logger = No_Logger)
  extends Resources(loaded_theories, known_theories, base_syntax, log)
{
  private val state = Synchronized(VSCode_Resources.State())


  /* document node name */

  def node_name(uri: String): Document.Node.Name =
  {
    val theory = Thy_Header.thy_name_bootstrap(uri).getOrElse("")
    val master_dir =
      if (!Url.is_wellformed_file(uri) || theory == "") ""
      else Url.file(uri).getCanonicalFile.getParent
    Document.Node.Name(uri, master_dir, theory)
  }

  override def import_name(qualifier: String, master: Document.Node.Name, s: String)
    : Document.Node.Name =
  {
    val name = super.import_name(qualifier, master, s)
    if (name.node.startsWith("file://") || name.node.forall(c => c != '/' && c != '\\')) name
    else name.copy(node = "file://" + name.node)
  }

  override def with_thy_reader[A](name: Document.Node.Name, f: Reader[Char] => A): A =
  {
    val uri = name.node
    get_model(uri) match {
      case Some(model) =>
        val reader = new CharSequenceReader(model.doc.make_text)
        f(reader)

      case None =>
        val file = Url.file(uri)
        if (!file.isFile) error("No such file: " + quote(file.toString))

        val reader = Scan.byte_reader(file)
        try { f(reader) } finally { reader.close }
    }
  }


  /* document models */

  def get_model(uri: String): Option[Document_Model] = state.value.models.get(uri)

  def update_model(session: Session, uri: String, text: String)
  {
    state.change(st =>
      {
        val model = st.models.getOrElse(uri, Document_Model.init(session, uri))
        val model1 = (model.update_text(text) getOrElse model).external(false)
        st.copy(
          models = st.models + (uri -> model1),
          pending_input = st.pending_input + uri)
      })
  }

  def close_model(uri: String): Option[Document_Model] =
    state.change_result(st =>
      st.models.get(uri) match {
        case None => (None, st)
        case Some(model) =>
          (Some(model), st.copy(models = st.models + (uri -> model.external(true))))
      })

  def sync_models(changed_files: Set[JFile]): Boolean =
    state.change_result(st =>
      {
        val changed_models =
          (for {
            (uri, model) <- st.models.iterator
            if changed_files(model.file)
            model1 <- model.update_file
          } yield (uri, model1)).toList
        if (changed_models.isEmpty) (false, st)
        else (true,
          st.copy(
            models = (st.models /: changed_models)(_ + _),
            pending_input = (st.pending_input /: changed_models.iterator.map(_._1))(_ + _)))
      })


  /* resolve dependencies */

  val thy_info = new Thy_Info(this)

  def resolve_dependencies(session: Session): Boolean =
  {
    state.change_result(st =>
      {
        val thys =
          (for ((_, model) <- st.models.iterator if model.is_theory)
           yield (model.node_name, Position.none)).toList

        val loaded_models =
          (for {
            dep <- thy_info.dependencies("", thys).deps.iterator
            uri = dep.name.node
            if !st.models.isDefinedAt(uri)
            text <-
              try { Some(File.read(Url.file(uri))) }
              catch { case ERROR(_) => None }
          }
          yield {
            val model = Document_Model.init(session, uri)
            val model1 = (model.update_text(text) getOrElse model).external(true)
            (uri, model1)
          }).toList

        if (loaded_models.isEmpty) (false, st)
        else
          (true,
            st.copy(
              models = st.models ++ loaded_models,
              pending_input = st.pending_input ++ loaded_models.iterator.map(_._1)))
      })
  }


  /* pending input */

  def flush_input(session: Session)
  {
    state.change(st =>
      {
        val changed_models =
          (for {
            uri <- st.pending_input.iterator
            model <- st.models.get(uri)
            res <- model.flush_edits
          } yield res).toList

        session.update(Document.Blobs.empty, changed_models.flatMap(_._1))
        st.copy(
          models = (st.models /: changed_models) { case (ms, (_, m)) => ms + (m.uri -> m) },
          pending_input = Set.empty)
      })
  }


  /* pending output */

  def update_output(changed_nodes: List[String]): Unit =
    state.change(st => st.copy(pending_output = st.pending_output ++ changed_nodes))

  def flush_output(channel: Channel)
  {
    state.change(st =>
      {
        val changed_iterator =
          for {
            uri <- st.pending_output.iterator
            model <- st.models.get(uri)
            rendering = model.rendering()
            (diagnostics, model1) <- model.publish_diagnostics(rendering)
          } yield {
            channel.diagnostics(model1.uri, rendering.diagnostics_output(diagnostics))
            model1
          }
        st.copy(
          models = (st.models /: changed_iterator) { case (ms, m) => ms + (m.uri -> m) },
          pending_output = Set.empty)
      }
    )
  }
}

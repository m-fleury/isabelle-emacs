/*  Title:      Pure/PIDE/document.scala
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Document
{
  /* unique identifiers */

  type State_ID = String
  type Command_ID = String
  type Version_ID = String

  val NO_ID = ""


  /* nodes */

  object Node { type Text_Edit = (String, List[isabelle.Text_Edit]) }  // FIXME None: remove

  type Edit[C] =
   (String,  // node name
    Option[List[(Option[C], Option[C])]])  // None: remove, Some: insert/remove commands


  /* command start positions */

  def command_starts(commands: Iterator[Command], offset: Int = 0): Iterator[(Command, Int)] =
  {
    var i = offset
    for (command <- commands) yield {
      val start = i
      i += command.length
      (command, start)
    }
  }


  /* initial document */

  val init: Document =
  {
    val doc = new Document(NO_ID, Map().withDefaultValue(Linear_Set()), Map())
    doc.assign_states(Nil)
    doc
  }



  /** document edits **/

  def text_edits(session: Session, old_doc: Document, new_id: Version_ID,
      edits: List[Node.Text_Edit]): (List[Edit[Command]], Document) =
  {
    require(old_doc.assignment.is_finished)


    /* unparsed dummy commands */

    def unparsed(source: String) =
      new Command(null, List(Token(Token.Kind.UNPARSED, source)))

    def is_unparsed(command: Command) = command.id == null


    /* phase 1: edit individual command source */

    @tailrec def edit_text(eds: List[Text_Edit],
        commands: Linear_Set[Command]): Linear_Set[Command] =
    {
      eds match {
        case e :: es =>
          command_starts(commands.iterator).find {
            case (cmd, cmd_start) =>
              e.can_edit(cmd.source, cmd_start) ||
                e.is_insert && e.start == cmd_start + cmd.length
          } match {
            case Some((cmd, cmd_start)) if e.can_edit(cmd.source, cmd_start) =>
              val (rest, text) = e.edit(cmd.source, cmd_start)
              val new_commands = commands.insert_after(Some(cmd), unparsed(text)) - cmd
              edit_text(rest.toList ::: es, new_commands)

            case Some((cmd, cmd_start)) =>
              edit_text(es, commands.insert_after(Some(cmd), unparsed(e.text)))

            case None =>
              require(e.is_insert && e.start == 0)
              edit_text(es, commands.insert_after(None, unparsed(e.text)))
          }
        case Nil => commands
      }
    }


    /* phase 2: recover command spans */

    @tailrec def parse_spans(commands: Linear_Set[Command]): Linear_Set[Command] =
    {
      commands.iterator.find(is_unparsed) match {
        case Some(first_unparsed) =>
          val first =
            commands.reverse_iterator(first_unparsed).find(_.is_command) getOrElse commands.head
          val last =
            commands.iterator(first_unparsed).find(_.is_command) getOrElse commands.last
          val range =
            commands.iterator(first).takeWhile(_ != last).toList ::: List(last)

          val sources = range.flatMap(_.span.map(_.source))
          val spans0 = Thy_Syntax.parse_spans(session.current_syntax.scan(sources.mkString))

          val (before_edit, spans1) =
            if (!spans0.isEmpty && first.is_command && first.span == spans0.head)
              (Some(first), spans0.tail)
            else (commands.prev(first), spans0)

          val (after_edit, spans2) =
            if (!spans1.isEmpty && last.is_command && last.span == spans1.last)
              (Some(last), spans1.take(spans1.length - 1))
            else (commands.next(last), spans1)

          val inserted = spans2.map(span => new Command(session.create_id(), span))
          val new_commands =
            commands.delete_between(before_edit, after_edit).append_after(before_edit, inserted)
          parse_spans(new_commands)

        case None => commands
      }
    }


    /* phase 3: resulting document edits */

    {
      val doc_edits = new mutable.ListBuffer[Edit[Command]]
      var nodes = old_doc.nodes
      var former_states = old_doc.assignment.join

      for ((name, text_edits) <- edits) {
        val commands0 = nodes(name)
        val commands1 = edit_text(text_edits, commands0)
        val commands2 = parse_spans(commands1)

        val removed_commands = commands0.iterator.filter(!commands2.contains(_)).toList
        val inserted_commands = commands2.iterator.filter(!commands0.contains(_)).toList

        val cmd_edits =
          removed_commands.reverse.map(cmd => (commands0.prev(cmd), None)) :::
          inserted_commands.map(cmd => (commands2.prev(cmd), Some(cmd)))

        doc_edits += (name -> Some(cmd_edits))
        nodes += (name -> commands2)
        former_states --= removed_commands
      }
      (doc_edits.toList, new Document(new_id, nodes, former_states))
    }
  }
}


class Document(
    val id: Document.Version_ID,
    val nodes: Map[String, Linear_Set[Command]],
    former_states: Map[Command, Command])  // FIXME !?
{
  /* command ranges */

  def commands(name: String): Linear_Set[Command] = nodes.get(name) getOrElse Linear_Set()

  def command_starts(name: String): Iterator[(Command, Int)] =
    Document.command_starts(commands(name).iterator)

  def command_start(name: String, cmd: Command): Option[Int] =
    command_starts(name).find(_._1 == cmd).map(_._2)

  def command_range(name: String, i: Int): Iterator[(Command, Int)] =
    command_starts(name) dropWhile { case (cmd, start) => start + cmd.length <= i }

  def command_range(name: String, i: Int, j: Int): Iterator[(Command, Int)] =
    command_range(name, i) takeWhile { case (_, start) => start < j }

  def command_at(name: String, i: Int): Option[(Command, Int)] =
  {
    val range = command_range(name, i)
    if (range.hasNext) Some(range.next) else None
  }

  def proper_command_at(name: String, i: Int): Option[Command] =
    command_at(name, i) match {
      case Some((command, _)) =>
        commands(name).reverse_iterator(command).find(cmd => !cmd.is_ignored)
      case None => None
    }


  /* command state assignment */

  val assignment = Future.promise[Map[Command, Command]]
  def await_assignment { assignment.join }

  @volatile private var tmp_states = former_states

  def assign_states(new_states: List[(Command, Command)])
  {
    assignment.fulfill(tmp_states ++ new_states)
    tmp_states = Map()
  }

  def current_state(cmd: Command): State =
  {
    require(assignment.is_finished)
    (assignment.join).get(cmd) match {
      case Some(cmd_state) => cmd_state.current_state
      case None => new State(cmd, Command.Status.UNDEFINED, 0, Nil, cmd.empty_markup)
    }
  }
}

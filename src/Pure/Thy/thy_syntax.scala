/*  Title:      Pure/Thy/thy_syntax.scala
    Author:     Makarius

Superficial theory syntax: tokens and spans.
*/

package isabelle


import scala.collection.mutable
import scala.annotation.tailrec


object Thy_Syntax
{
  /** perspective **/

  def command_perspective(
      node: Document.Node,
      perspective: Text.Perspective,
      overlays: Document.Node.Overlays): (Command.Perspective, Command.Perspective) =
  {
    if (perspective.is_empty && overlays.is_empty)
      (Command.Perspective.empty, Command.Perspective.empty)
    else {
      val has_overlay = overlays.commands
      val visible = new mutable.ListBuffer[Command]
      val visible_overlay = new mutable.ListBuffer[Command]
      @tailrec
      def check_ranges(ranges: List[Text.Range], commands: Stream[(Command, Text.Offset)])
      {
        (ranges, commands) match {
          case (range :: more_ranges, (command, offset) #:: more_commands) =>
            val command_range = command.range + offset
            range compare command_range match {
              case 0 =>
                visible += command
                visible_overlay += command
                check_ranges(ranges, more_commands)
              case c =>
                if (has_overlay(command)) visible_overlay += command

                if (c < 0) check_ranges(more_ranges, commands)
                else check_ranges(ranges, more_commands)
            }

          case (Nil, (command, _) #:: more_commands) =>
            if (has_overlay(command)) visible_overlay += command

            check_ranges(Nil, more_commands)

          case _ =>
        }
      }

      val commands =
        (if (overlays.is_empty) node.command_iterator(perspective.range)
         else node.command_iterator()).toStream
      check_ranges(perspective.ranges, commands)
      (Command.Perspective(visible.toList), Command.Perspective(visible_overlay.toList))
    }
  }



  /** header edits: structure and outer syntax **/

  private def header_edits(
    resources: Resources,
    previous: Document.Version,
    edits: List[Document.Edit_Text]):
    (List[Document.Node.Name], Document.Nodes, List[Document.Edit_Command]) =
  {
    val syntax_changed0 = new mutable.ListBuffer[Document.Node.Name]
    var nodes = previous.nodes
    val doc_edits = new mutable.ListBuffer[Document.Edit_Command]

    edits foreach {
      case (name, Document.Node.Deps(header)) =>
        val node = nodes(name)
        val update_header =
          !node.header.errors.isEmpty || !header.errors.isEmpty || node.header != header
        if (update_header) {
          val node1 = node.update_header(header)
          if (node.header.imports != node1.header.imports ||
              node.header.keywords != node1.header.keywords) syntax_changed0 += name
          nodes += (name -> node1)
          doc_edits += (name -> Document.Node.Deps(header))
        }
      case _ =>
    }

    val syntax_changed = nodes.descendants(syntax_changed0.toList)

    for (name <- syntax_changed) {
      val node = nodes(name)
      val syntax =
        if (node.is_empty) None
        else {
          val imports_syntax = node.header.imports.flatMap(a => nodes(a).syntax)
          Some((resources.base_syntax /: imports_syntax)(_ ++ _).add_keywords(node.header.keywords))
        }
      nodes += (name -> node.update_syntax(syntax))
    }

    (syntax_changed, nodes, doc_edits.toList)
  }



  /** text edits **/

  /* edit individual command source */

  @tailrec def edit_text(eds: List[Text.Edit], commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    eds match {
      case e :: es =>
        Document.Node.Commands.starts(commands.iterator).find {
          case (cmd, cmd_start) =>
            e.can_edit(cmd.source, cmd_start) ||
              e.is_insert && e.start == cmd_start + cmd.length
        } match {
          case Some((cmd, cmd_start)) if e.can_edit(cmd.source, cmd_start) =>
            val (rest, text) = e.edit(cmd.source, cmd_start)
            val new_commands = commands.insert_after(Some(cmd), Command.unparsed(text)) - cmd
            edit_text(rest.toList ::: es, new_commands)

          case Some((cmd, cmd_start)) =>
            edit_text(es, commands.insert_after(Some(cmd), Command.unparsed(e.text)))

          case None =>
            require(e.is_insert && e.start == 0)
            edit_text(es, commands.insert_after(None, Command.unparsed(e.text)))
        }
      case Nil => commands
    }
  }


  /* reparse range of command spans */

  @tailrec private def chop_common(
      cmds: List[Command],
      blobs_spans: List[(List[Command.Blob], Command_Span.Span)])
    : (List[Command], List[(List[Command.Blob], Command_Span.Span)]) =
  {
    (cmds, blobs_spans) match {
      case (cmd :: cmds, (blobs, span) :: rest) if cmd.blobs == blobs && cmd.span == span =>
        chop_common(cmds, rest)
      case _ => (cmds, blobs_spans)
    }
  }

  private def reparse_spans(
    resources: Resources,
    syntax: Prover.Syntax,
    get_blob: Document.Node.Name => Option[Document.Blob],
    name: Document.Node.Name,
    commands: Linear_Set[Command],
    first: Command, last: Command): Linear_Set[Command] =
  {
    val cmds0 = commands.iterator(first, last).toList
    val blobs_spans0 =
      syntax.parse_spans(cmds0.iterator.map(_.source).mkString).
        map(span => (Command_Span.resolve_files(resources, syntax, name, span, get_blob), span))

    val (cmds1, blobs_spans1) = chop_common(cmds0, blobs_spans0)

    val (rev_cmds2, rev_blobs_spans2) = chop_common(cmds1.reverse, blobs_spans1.reverse)
    val cmds2 = rev_cmds2.reverse
    val blobs_spans2 = rev_blobs_spans2.reverse

    cmds2 match {
      case Nil =>
        assert(blobs_spans2.isEmpty)
        commands
      case cmd :: _ =>
        val hook = commands.prev(cmd)
        val inserted =
          blobs_spans2.map({ case (blobs, span) => Command(Document_ID.make(), name, blobs, span) })
        (commands /: cmds2)(_ - _).append_after(hook, inserted)
    }
  }


  /* recover command spans after edits */

  // FIXME somewhat slow
  private def recover_spans(
    resources: Resources,
    syntax: Prover.Syntax,
    get_blob: Document.Node.Name => Option[Document.Blob],
    name: Document.Node.Name,
    perspective: Command.Perspective,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    val visible = perspective.commands.toSet

    def next_invisible_command(cmds: Linear_Set[Command], from: Command): Command =
      cmds.iterator(from).dropWhile(cmd => !cmd.is_proper || visible(cmd))
        .find(_.is_proper) getOrElse cmds.last

    @tailrec def recover(cmds: Linear_Set[Command]): Linear_Set[Command] =
      cmds.find(_.is_unparsed) match {
        case Some(first_unparsed) =>
          val first = next_invisible_command(cmds.reverse, first_unparsed)
          val last = next_invisible_command(cmds, first_unparsed)
          recover(reparse_spans(resources, syntax, get_blob, name, cmds, first, last))
        case None => cmds
      }
    recover(commands)
  }


  /* consolidate unfinished spans */

  private def consolidate_spans(
    resources: Resources,
    syntax: Prover.Syntax,
    get_blob: Document.Node.Name => Option[Document.Blob],
    reparse_limit: Int,
    name: Document.Node.Name,
    perspective: Command.Perspective,
    commands: Linear_Set[Command]): Linear_Set[Command] =
  {
    if (perspective.commands.isEmpty) commands
    else {
      commands.find(_.is_unfinished) match {
        case Some(first_unfinished) =>
          val visible = perspective.commands.toSet
          commands.reverse.find(visible) match {
            case Some(last_visible) =>
              val it = commands.iterator(last_visible)
              var last = last_visible
              var i = 0
              while (i < reparse_limit && it.hasNext) {
                last = it.next
                i += last.length
              }
              reparse_spans(resources, syntax, get_blob, name, commands, first_unfinished, last)
            case None => commands
          }
        case None => commands
      }
    }
  }


  /* main */

  def diff_commands(old_cmds: Linear_Set[Command], new_cmds: Linear_Set[Command])
    : List[Command.Edit] =
  {
    val removed = old_cmds.iterator.filter(!new_cmds.contains(_)).toList
    val inserted = new_cmds.iterator.filter(!old_cmds.contains(_)).toList

    removed.reverse.map(cmd => (old_cmds.prev(cmd), None)) :::
    inserted.map(cmd => (new_cmds.prev(cmd), Some(cmd)))
  }

  private def text_edit(
    resources: Resources,
    syntax: Prover.Syntax,
    get_blob: Document.Node.Name => Option[Document.Blob],
    reparse_limit: Int,
    node: Document.Node, edit: Document.Edit_Text): Document.Node =
  {
    edit match {
      case (_, Document.Node.Clear()) => node.clear

      case (_, Document.Node.Blob(blob)) => node.init_blob(blob)

      case (name, Document.Node.Edits(text_edits)) =>
        if (name.is_theory) {
          val commands0 = node.commands
          val commands1 = edit_text(text_edits, commands0)
          val commands2 =
            recover_spans(resources, syntax, get_blob, name, node.perspective.visible, commands1)
          node.update_commands(commands2)
        }
        else node

      case (_, Document.Node.Deps(_)) => node

      case (name, Document.Node.Perspective(required, text_perspective, overlays)) =>
        val (visible, visible_overlay) = command_perspective(node, text_perspective, overlays)
        val perspective: Document.Node.Perspective_Command =
          Document.Node.Perspective(required, visible_overlay, overlays)
        if (node.same_perspective(perspective)) node
        else
          node.update_perspective(perspective).update_commands(
            consolidate_spans(resources, syntax, get_blob, reparse_limit,
              name, visible, node.commands))
    }
  }

  def parse_change(
      resources: Resources,
      reparse_limit: Int,
      previous: Document.Version,
      doc_blobs: Document.Blobs,
      edits: List[Document.Edit_Text]): Session.Change =
  {
    def get_blob(name: Document.Node.Name) =
      doc_blobs.get(name) orElse previous.nodes(name).get_blob

    val (syntax_changed, nodes0, doc_edits0) = header_edits(resources, previous, edits)

    val (doc_edits, version) =
      if (edits.isEmpty) (Nil, Document.Version.make(previous.nodes))
      else {
        val reparse =
          (syntax_changed /: nodes0.iterator)({
            case (reparse, (name, node)) =>
              if (node.load_commands.exists(_.blobs_changed(doc_blobs)))
                name :: reparse
              else reparse
            })
        val reparse_set = reparse.toSet

        var nodes = nodes0
        val doc_edits = new mutable.ListBuffer[Document.Edit_Command]; doc_edits ++= doc_edits0

        val node_edits =
          (edits ::: reparse.map((_, Document.Node.Edits(Nil)))).groupBy(_._1)
            .asInstanceOf[Map[Document.Node.Name, List[Document.Edit_Text]]]  // FIXME ???

        node_edits foreach {
          case (name, edits) =>
            val node = nodes(name)
            val syntax = node.syntax getOrElse resources.base_syntax
            val commands = node.commands

            val node1 =
              if (reparse_set(name) && !commands.isEmpty)
                node.update_commands(
                  reparse_spans(resources, syntax, get_blob,
                    name, commands, commands.head, commands.last))
              else node
            val node2 =
              (node1 /: edits)(text_edit(resources, syntax, get_blob, reparse_limit, _, _))

            if (!(node.same_perspective(node2.perspective)))
              doc_edits += (name -> node2.perspective)

            doc_edits += (name -> Document.Node.Edits(diff_commands(commands, node2.commands)))

            nodes += (name -> node2)
        }
        (doc_edits.toList.filterNot(_._2.is_void), Document.Version.make(nodes))
      }

    Session.Change(previous, syntax_changed, !syntax_changed.isEmpty, doc_edits, version)
  }
}

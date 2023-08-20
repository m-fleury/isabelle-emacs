/*  Title:      Tools/VSCode/src/dynamic_output.scala
    Author:     Makarius

Dynamic output, depending on caret focus: messages, state etc.
*/

package isabelle.vscode


import isabelle._


object Dynamic_Output {
  sealed case class State(val server: vscode.Language_Server, do_update: Boolean = true, output: List[XML.Tree] = Nil) {
    def handle_update(
      resources: VSCode_Resources,
      channel: Channel,
      restriction: Option[Set[Command]]
    ): State = {
      val st1 =
        resources.get_caret() match {
          case None => copy(output = Nil)
          case Some(caret) =>
            val snapshot = resources.snapshot(caret.model)
            if (do_update && !snapshot.is_outdated) {
              snapshot.current_command(caret.node_name, caret.offset) match {
                case None => copy(output = Nil)
                case Some(command) =>
                  copy(output =
                    if (restriction.isEmpty || restriction.get.contains(command)) {
                      val output_state = true // resources.options.bool("editor_output_state")
                        Rendering.output_messages(snapshot.command_results(command), output_state)
                    } else output)
              }
            }
            else this
        }
      if (st1.output != output) {
        if(server.html_output) {
          val node_context =
            new Browser_Info.Node_Context {
              override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
                for {
                  thy_file <- Position.Def_File.unapply(props)
                  def_line <- Position.Def_Line.unapply(props)
                  source <- resources.source_file(thy_file)
                  uri = File.uri(Path.explode(source).absolute_file)
                } yield HTML.link(uri.toString + "#" + def_line, body)
            }
          // using this to distinguish between VSCode and emacs is a hack
          if (resources.options.bool("vscode_unicode_symbols")) {// if VSCode
            val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)
            val html = node_context.make_html(elements, Pretty.separate(st1.output))
            channel.write(LSP.Dynamic_Output(HTML.source(html).toString))
          }
        } else {
          // emacs. The HTML is very similar (and actually contains more informations).
          val content =
            cat_lines(
              List(HTML.output(XML.elem("body", List(HTML.source(Pretty.formatted(st1.output, margin = resources.get_message_margin())))),
                hidden = false, structural = false)))
          val encoded_content = Symbol.encode(content)
          channel.write(LSP.Dynamic_Output(encoded_content))
        }
      } else {
        channel.write(LSP.Dynamic_Output(resources.output_pretty_message(Pretty.separate(st1.output))))
      }
      st1
    }

    def force_update(
      resources: VSCode_Resources, channel: Channel, restriction: Option[Set[Command]]): State =
    {
      val st1 =
        resources.get_caret() match {
          case None => copy(output = Nil)
          case Some(caret) =>
            val snapshot = resources.snapshot(caret.model)
            if (do_update && !snapshot.is_outdated) {
              snapshot.current_command(caret.node_name, caret.offset) match {
                case None => copy(output = Nil)
                case Some(command) =>
                  val text =
                    if (!restriction.isDefined || restriction.get.contains(command)) {
                      //server.resources.output_pretty_message(snapshot.command_results(command))
                      val output_state = resources.options.bool("editor_output_state")
                      Rendering.output_messages(snapshot.command_results(command), output_state)
                    } else output
                  copy(output = text)
              }
            }
            else this
        }

      if(server.html_output) {
        val node_context =
          new Browser_Info.Node_Context {
            override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
              for {
                thy_file <- Position.Def_File.unapply(props)
                def_line <- Position.Def_Line.unapply(props)
                source <- resources.source_file(thy_file)
                uri = File.uri(Path.explode(source).absolute_file)
              } yield HTML.link(uri.toString + "#" + def_line, body)
          }
        // using this to distinguish between VSCode and emacs is a hack
        if (resources.options.bool("vscode_unicode_symbols")) {// if VSCode
          val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)
          val html = node_context.make_html(elements, Pretty.formatted(st1.output, margin = resources.get_message_margin()))
          channel.write(LSP.Dynamic_Output(HTML.source(html).toString))
        }
        else {
          // emacs. The HTML is very similar (and actually contains more informations).
          val content =
            cat_lines(
              List(HTML.output(XML.elem("body", List(HTML.source(Pretty.formatted(st1.output, margin = resources.get_message_margin())))),
                hidden = false, structural = false)))
          val encoded_content = Symbol.encode(content)
          channel.write(LSP.Dynamic_Output(encoded_content))
        }
      } else {
        channel.write(LSP.Dynamic_Output(resources.output_pretty_message(Pretty.separate(st1.output))))
      }
      st1
    }
  }

  def apply(server: Language_Server): Dynamic_Output = new Dynamic_Output(server)
}


class Dynamic_Output private(server: Language_Server) {
  private val state = Synchronized(Dynamic_Output.State(server))

  private def handle_update(restriction: Option[Set[Command]]): Unit =
    state.change(_.handle_update(server.resources, server.channel, restriction))

  private def force_update(restriction: Option[Set[Command]]): Unit =
    state.change(_.force_update(server.resources, server.channel, restriction))

  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        handle_update(if (changed.assignment) None else Some(changed.commands))

      case Session.Caret_Focus =>
        handle_update(None)
    }

  def init(): Unit = {
    server.session.commands_changed += main
    server.session.caret_focus += main
    handle_update(None)
  }

  def exit(): Unit = {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }

  def force_goal_reprint(): Unit =
  {
    force_update(None)
  }
}

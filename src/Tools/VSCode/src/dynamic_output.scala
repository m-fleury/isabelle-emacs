/*  Title:      Tools/VSCode/src/dynamic_output.scala
    Author:     Makarius

Dynamic output, depending on caret focus: messages, state etc.
*/

package isabelle.vscode


import isabelle._


object Dynamic_Output
{
  sealed case class State(val server: vscode.Language_Server, do_update: Boolean = true, output: List[XML.Tree] = Nil)
  {
    def handle_update(
      resources: VSCode_Resources, channel: Channel, restriction: Option[Set[Command]]): State =
    {
      val st1 =
        resources.get_caret() match {
          case None => copy(output = Nil)
          case Some(caret) =>
            val snapshot = caret.model.snapshot()
            if (do_update && !snapshot.is_outdated) {
              snapshot.current_command(caret.node_name, caret.offset) match {
                case None => copy(output = Nil)
                case Some(command) =>
                  val text = 
                    if (!restriction.isDefined || restriction.get.contains(command))
                      //server.resources.output_pretty_message(snapshot.command_results(command))
                      Rendering.output_messages(snapshot.command_results(command))
                    else output
                  copy(output = text)
              }
            }
            else this
        }
      if (st1.output != output) {
        val content =
          cat_lines(
            List(HTML.output(XML.elem("body", List(HTML.source(Pretty.formatted(st1.output, margin = resources.get_message_margin())))),
            hidden = false, structural = true)))
        channel.write(LSP.Dynamic_Output(content))
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
            val snapshot = caret.model.snapshot()
            if (do_update && !snapshot.is_outdated) {
              snapshot.current_command(caret.node_name, caret.offset) match {
                case None => copy(output = Nil)
                case Some(command) =>
                  val text = 
                    if (!restriction.isDefined || restriction.get.contains(command))
                      //server.resources.output_pretty_message(snapshot.command_results(command))
                      Rendering.output_messages(snapshot.command_results(command))
                    else output
                  copy(output = text)
              }
            }
            else this
        }
      val content =
        cat_lines(
          List(HTML.output(XML.elem("body", List(HTML.source(Pretty.formatted(st1.output, margin = resources.get_message_margin())))),
            hidden = false, structural = true)))
      channel.write(LSP.Dynamic_Output(content))
      st1
    }
  }

  def apply(server: Language_Server): Dynamic_Output = new Dynamic_Output(server)
}


class Dynamic_Output private(server: Language_Server)
{
  private val state = Synchronized(Dynamic_Output.State(server))

  private def handle_update(restriction: Option[Set[Command]])
  { state.change(_.handle_update(server.resources, server.channel, restriction)) }


  private def force_update(restriction: Option[Set[Command]])
  { state.change(_.force_update(server.resources, server.channel, restriction)) }

  /* main */

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        handle_update(if (changed.assignment) None else Some(changed.commands))

      case Session.Caret_Focus =>
        handle_update(None)
    }

  def init()
  {
    server.session.commands_changed += main
    server.session.caret_focus += main
    handle_update(None)
  }

  def exit()
  {
    server.session.commands_changed -= main
    server.session.caret_focus -= main
  }

  def force_goal_reprint()
  {
    force_update(None)
  }
}

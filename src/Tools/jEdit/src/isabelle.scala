/*  Title:      Tools/jEdit/src/isabelle.scala
    Author:     Makarius

Global configuration and convenience operations for Isabelle/jEdit.
*/

package isabelle.jedit


import isabelle._

import java.awt.Frame

import scala.swing.CheckBox
import scala.swing.event.ButtonClicked

import org.gjt.sp.jedit.{jEdit, View, Buffer}
import org.gjt.sp.jedit.buffer.JEditBuffer
import org.gjt.sp.jedit.textarea.{JEditTextArea, StructureMatcher}
import org.gjt.sp.jedit.syntax.TokenMarker
import org.gjt.sp.jedit.gui.{DockableWindowManager, CompleteWord}
import org.jedit.options.CombinedOptions


object Isabelle
{
  /* editor modes */

  val modes =
    List(
      "isabelle",         // theory source
      "isabelle-ml",      // ML source
      "isabelle-news",    // NEWS
      "isabelle-options", // etc/options
      "isabelle-output",  // pretty text area output
      "isabelle-root",    // session ROOT
      "sml")              // Standard ML (not Isabelle/ML)

  private lazy val ml_syntax: Outer_Syntax =
    Outer_Syntax.init().no_tokens.
      set_language_context(Completion.Language_Context.ML_outer)

  private lazy val sml_syntax: Outer_Syntax =
    Outer_Syntax.init().no_tokens.
      set_language_context(Completion.Language_Context.SML_outer)

  private lazy val news_syntax: Outer_Syntax =
    Outer_Syntax.init().no_tokens

  def mode_syntax(mode: String): Option[Outer_Syntax] =
    mode match {
      case "isabelle" => Some(PIDE.resources.base_syntax.asInstanceOf[Outer_Syntax])
      case "isabelle-options" => Some(Options.options_syntax)
      case "isabelle-root" => Some(Build.root_syntax)
      case "isabelle-ml" => Some(ml_syntax)
      case "isabelle-news" => Some(news_syntax)
      case "isabelle-output" => None
      case "sml" => Some(sml_syntax)
      case _ => None
    }

  def buffer_syntax(buffer: JEditBuffer): Option[Outer_Syntax] =
    (JEdit_Lib.buffer_mode(buffer), PIDE.document_model(buffer)) match {
      case ("isabelle", Some(model)) =>
        Some(PIDE.session.recent_syntax(model.node_name).asInstanceOf[Outer_Syntax])
      case (mode, _) => mode_syntax(mode)
    }


  /* token markers */

  private val mode_markers: Map[String, TokenMarker] =
    Map(modes.map(mode => (mode, new Token_Markup.Marker(mode, None))): _*) +
      ("bibtex" -> new Bibtex_JEdit.Token_Marker)

  def mode_token_marker(mode: String): Option[TokenMarker] = mode_markers.get(mode)

  def buffer_token_marker(buffer: Buffer): Option[TokenMarker] =
  {
    val mode = JEdit_Lib.buffer_mode(buffer)
    if (mode == "isabelle") Some(new Token_Markup.Marker(mode, Some(buffer)))
    else mode_token_marker(mode)
  }


  /* structure matchers */

  def structure_matchers(name: String): List[StructureMatcher] =
    if (name == "isabelle") List(Structure_Matching.Isabelle_Matcher) else Nil


  /* dockable windows */

  private def wm(view: View): DockableWindowManager = view.getDockableWindowManager

  def debugger_dockable(view: View): Option[Debugger_Dockable] =
    wm(view).getDockableWindow("isabelle-debugger") match {
      case dockable: Debugger_Dockable => Some(dockable)
      case _ => None
    }

  def documentation_dockable(view: View): Option[Documentation_Dockable] =
    wm(view).getDockableWindow("isabelle-documentation") match {
      case dockable: Documentation_Dockable => Some(dockable)
      case _ => None
    }

  def monitor_dockable(view: View): Option[Monitor_Dockable] =
    wm(view).getDockableWindow("isabelle-monitor") match {
      case dockable: Monitor_Dockable => Some(dockable)
      case _ => None
    }

  def output_dockable(view: View): Option[Output_Dockable] =
    wm(view).getDockableWindow("isabelle-output") match {
      case dockable: Output_Dockable => Some(dockable)
      case _ => None
    }

  def protocol_dockable(view: View): Option[Protocol_Dockable] =
    wm(view).getDockableWindow("isabelle-protocol") match {
      case dockable: Protocol_Dockable => Some(dockable)
      case _ => None
    }

  def query_dockable(view: View): Option[Query_Dockable] =
    wm(view).getDockableWindow("isabelle-query") match {
      case dockable: Query_Dockable => Some(dockable)
      case _ => None
    }

  def raw_output_dockable(view: View): Option[Raw_Output_Dockable] =
    wm(view).getDockableWindow("isabelle-raw-output") match {
      case dockable: Raw_Output_Dockable => Some(dockable)
      case _ => None
    }

  def simplifier_trace_dockable(view: View): Option[Simplifier_Trace_Dockable] =
    wm(view).getDockableWindow("isabelle-simplifier-trace") match {
      case dockable: Simplifier_Trace_Dockable => Some(dockable)
      case _ => None
    }

  def sledgehammer_dockable(view: View): Option[Sledgehammer_Dockable] =
    wm(view).getDockableWindow("isabelle-sledgehammer") match {
      case dockable: Sledgehammer_Dockable => Some(dockable)
      case _ => None
    }

  def state_dockable(view: View): Option[State_Dockable] =
    wm(view).getDockableWindow("isabelle-state") match {
      case dockable: State_Dockable => Some(dockable)
      case _ => None
    }

  def symbols_dockable(view: View): Option[Symbols_Dockable] =
    wm(view).getDockableWindow("isabelle-symbols") match {
      case dockable: Symbols_Dockable => Some(dockable)
      case _ => None
    }

  def syslog_dockable(view: View): Option[Syslog_Dockable] =
    wm(view).getDockableWindow("isabelle-syslog") match {
      case dockable: Syslog_Dockable => Some(dockable)
      case _ => None
    }

  def theories_dockable(view: View): Option[Theories_Dockable] =
    wm(view).getDockableWindow("isabelle-theories") match {
      case dockable: Theories_Dockable => Some(dockable)
      case _ => None
    }

  def timing_dockable(view: View): Option[Timing_Dockable] =
    wm(view).getDockableWindow("isabelle-timing") match {
      case dockable: Timing_Dockable => Some(dockable)
      case _ => None
    }


  /* continuous checking */

  private val CONTINUOUS_CHECKING = "editor_continuous_checking"

  def continuous_checking: Boolean = PIDE.options.bool(CONTINUOUS_CHECKING)
  def continuous_checking_=(b: Boolean): Unit =
    GUI_Thread.require {
      if (continuous_checking != b) {
        PIDE.options.bool(CONTINUOUS_CHECKING) = b
        PIDE.session.update_options(PIDE.options.value)
      }
    }

  def set_continuous_checking() { continuous_checking = true }
  def reset_continuous_checking() { continuous_checking = false }
  def toggle_continuous_checking() { continuous_checking = !continuous_checking }

  class Continuous_Checking extends CheckBox("Continuous checking")
  {
    tooltip = "Continuous checking of proof document (visible and required parts)"
    reactions += { case ButtonClicked(_) => continuous_checking = selected }
    def load() { selected = continuous_checking }
    load()
  }


  /* update state */

  def update_state(view: View): Unit =
    state_dockable(view).foreach(_.update_request())


  /* ML statistics */

  class ML_Stats extends
    JEdit_Options.Check_Box("ML_statistics", "ML statistics", "Enable ML runtime system statistics")


  /* required document nodes */

  private def node_required_update(view: View, toggle: Boolean = false, set: Boolean = false)
  {
    GUI_Thread.require {}
    PIDE.document_model(view.getBuffer) match {
      case Some(model) =>
        model.node_required = (if (toggle) !model.node_required else set)
      case None =>
    }
  }

  def set_node_required(view: View) { node_required_update(view, set = true) }
  def reset_node_required(view: View) { node_required_update(view, set = false) }
  def toggle_node_required(view: View) { node_required_update(view, toggle = true) }


  /* font size */

  def reset_font_size() {
    Font_Info.main_change.reset(PIDE.options.int("jedit_reset_font_size").toFloat)
  }
  def increase_font_size() { Font_Info.main_change.step(1) }
  def decrease_font_size() { Font_Info.main_change.step(-1) }


  /* structured edits */

  def insert_line_padding(text_area: JEditTextArea, text: String)
  {
    val buffer = text_area.getBuffer
    JEdit_Lib.buffer_edit(buffer) {
      val text1 =
        if (text_area.getSelectionCount == 0) {
          def pad(range: Text.Range): String =
            if (JEdit_Lib.try_get_text(buffer, range) == Some("\n")) "" else "\n"

          val caret = JEdit_Lib.caret_range(text_area)
          val before_caret = JEdit_Lib.point_range(buffer, caret.start - 1)
          pad(before_caret) + text + pad(caret)
        }
        else text
      text_area.setSelectedText(text1)
    }
  }

  def edit_command(
    snapshot: Document.Snapshot,
    buffer: Buffer,
    padding: Boolean,
    id: Document_ID.Generic,
    s: String)
  {
    if (!snapshot.is_outdated) {
      (snapshot.state.find_command(snapshot.version, id), PIDE.document_model(buffer)) match {
        case (Some((node, command)), Some(model)) if command.node_name == model.node_name =>
          node.command_start(command) match {
            case Some(start) =>
              JEdit_Lib.buffer_edit(buffer) {
                val range = command.proper_range + start
                if (padding) {
                  buffer.insert(start + range.length, "\n" + s)
                }
                else {
                  buffer.remove(start, range.length)
                  buffer.insert(start, s)
                }
              }
            case None =>
          }
        case _ =>
      }
    }
  }


  /* completion */

  def complete(view: View, word_only: Boolean)
  {
    Completion_Popup.Text_Area.action(view.getTextArea, word_only)
  }


  /* control styles */

  def control_sub(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.sub) }

  def control_sup(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.sup) }

  def control_bold(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.bold) }

  def control_emph(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, Symbol.emph) }

  def control_reset(text_area: JEditTextArea)
  { Token_Markup.edit_control_style(text_area, "") }


  /* block styles */

  private def enclose_input(text_area: JEditTextArea, s1: String, s2: String)
  {
    s1.foreach(text_area.userInput(_))
    s2.foreach(text_area.userInput(_))
    s2.foreach(_ => text_area.goToPrevCharacter(false))
  }

  def input_bsub(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsub_decoded, Symbol.esub_decoded) }

  def input_bsup(text_area: JEditTextArea)
  { enclose_input(text_area, Symbol.bsup_decoded, Symbol.esup_decoded) }


  /* spell-checker dictionary */

  def update_dictionary(text_area: JEditTextArea, include: Boolean, permanent: Boolean)
  {
    for {
      spell_checker <- PIDE.spell_checker.get
      doc_view <- PIDE.document_view(text_area)
      rendering = doc_view.get_rendering()
      range = JEdit_Lib.caret_range(text_area)
      Text.Info(_, word) <- Spell_Checker.current_word(text_area, rendering, range)
    } {
      spell_checker.update(word, include, permanent)
      JEdit_Lib.jedit_views().foreach(_.repaint())
    }
  }

  def reset_dictionary()
  {
    for (spell_checker <- PIDE.spell_checker.get)
    {
      spell_checker.reset()
      JEdit_Lib.jedit_views().foreach(_.repaint())
    }
  }


  /* debugger */

  def toggle_breakpoint(text_area: JEditTextArea): Unit =
    if (Debugger.is_active()) {
      for {
        (command, serial) <- Debugger_Dockable.get_breakpoint(text_area, text_area.getCaretPosition)
      } Debugger_Dockable.toggle_breakpoint(command, serial)
    }


  /* plugin options */

  def plugin_options(frame: Frame)
  {
    GUI_Thread.require {}
    jEdit.setProperty("Plugin Options.last", "isabelle-general")
    new CombinedOptions(frame, 1)
  }
}

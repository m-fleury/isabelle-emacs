/*  Title:      Tools/jEdit/src/theories_status.scala
    Author:     Makarius

GUI panel for status of theories.
*/

package isabelle.jedit


import isabelle._

import scala.swing.{ListView, Alignment, Label, CheckBox, BorderPanel, BoxPanel, Orientation,
  Component}
import scala.swing.event.{MouseClicked, MouseMoved}

import java.awt.{BorderLayout, Graphics2D, Color, Point, Dimension}
import javax.swing.border.{BevelBorder, SoftBevelBorder}
import javax.swing.{JList, BorderFactory, UIManager}

import org.gjt.sp.jedit.View


class Theories_Status(view: View) {
  /* component state -- owned by GUI thread */

  private var nodes_status = Document_Status.Nodes_Status.empty
  private var theory_required: Set[Document.Node.Name] = Document_Model.required_nodes(false)
  private var document_required: Set[Document.Node.Name] = Document_Model.required_nodes(true)


  /* node renderer */

  private class Geometry {
    private var location: Point = null
    private var size: Dimension = null

    def in(location0: Point, p: Point): Boolean =
      location != null && size != null && location0 != null && p != null && {
        val x = location0.x + location.x
        val y = location0.y + location.y
        x <= p.x && p.x < x + size.width &&
        y <= p.y && p.y < y + size.height
      }

    def update(new_location: Point, new_size: Dimension): Unit = {
      if (new_location != null && new_size != null) {
        location = new_location
        size = new_size
      }
    }
  }

  private class Required extends CheckBox {
    val geometry = new Geometry
    opaque = false
    override def paintComponent(gfx: Graphics2D): Unit = {
      super.paintComponent(gfx)
      geometry.update(location, size)
    }
  }

  private object Node_Renderer_Component extends BorderPanel {
    opaque = true
    border = BorderFactory.createEmptyBorder(2, 2, 2, 2)

    var node_name: Document.Node.Name = Document.Node.Name.empty

    val theory_required = new Required
    val document_required = new Required

    val label_geometry = new Geometry
    val label: Label = new Label {
      background = view.getTextArea.getPainter.getBackground
      foreground = view.getTextArea.getPainter.getForeground
      opaque = false
      xAlignment = Alignment.Leading

      override def paintComponent(gfx: Graphics2D): Unit = {
        def paint_segment(x: Int, w: Int, color: Color): Unit = {
          gfx.setColor(color)
          gfx.fillRect(x, 0, w, size.height)
        }

        paint_segment(0, size.width, background)
        nodes_status.get(node_name) match {
          case Some(node_status) =>
            val segments =
              List(
                (node_status.unprocessed, PIDE.options.color_value("unprocessed1_color")),
                (node_status.running, PIDE.options.color_value("running_color")),
                (node_status.warned, PIDE.options.color_value("warning_color")),
                (node_status.failed, PIDE.options.color_value("error_color"))
              ).filter(_._1 > 0)

            segments.foldLeft(size.width - 2) {
              case (last, (n, color)) =>
                val w = (n * ((size.width - 4) - segments.length) / node_status.total) max 4
                paint_segment(last - w, w, color)
                last - w - 1
              }

          case None =>
            paint_segment(0, size.width, PIDE.options.color_value("unprocessed1_color"))
        }
        super.paintComponent(gfx)

        label_geometry.update(location, size)
      }
    }

    def label_border(name: Document.Node.Name): Unit = {
      val st = nodes_status.overall_node_status(name)
      val color =
        st match {
          case Document_Status.Overall_Node_Status.ok =>
            PIDE.options.color_value("ok_color")
          case Document_Status.Overall_Node_Status.failed =>
            PIDE.options.color_value("failed_color")
          case _ => label.foreground
        }
      val thickness1 = if (st == Document_Status.Overall_Node_Status.pending) 1 else 3
      val thickness2 = 4 - thickness1

      label.border =
        BorderFactory.createCompoundBorder(
          BorderFactory.createLineBorder(color, thickness1),
          BorderFactory.createEmptyBorder(thickness2, thickness2, thickness2, thickness2))
    }

    val required = new BoxPanel(Orientation.Horizontal)
    required.contents += theory_required
    // FIXME required.contents += document_required

    layout(required) = BorderPanel.Position.West
    layout(label) = BorderPanel.Position.Center
  }

  private def in_required(location0: Point, p: Point, document: Boolean = false): Boolean =
    Node_Renderer_Component != null && {
      val required =
        if (document) Node_Renderer_Component.document_required
        else Node_Renderer_Component.theory_required
      required.geometry.in(location0, p)
    }

  private def in_label(location0: Point, p: Point): Boolean =
    Node_Renderer_Component != null && Node_Renderer_Component.label_geometry.in(location0, p)

  private class Node_Renderer extends ListView.Renderer[Document.Node.Name] {
    def componentFor(
      list: ListView[_ <: isabelle.Document.Node.Name],
      isSelected: Boolean,
      focused: Boolean,
      name: Document.Node.Name,
      index: Int
    ): Component = {
      val component = Node_Renderer_Component
      component.node_name = name
      component.theory_required.selected = theory_required.contains(name)
      component.document_required.selected = document_required.contains(name)
      component.label_border(name)
      component.label.text = name.theory_base_name
      component
    }
  }


  /* GUI component */

  val gui: ListView[Document.Node.Name] = new ListView[Document.Node.Name](Nil) {
    background = {
      // enforce default value
      val c = UIManager.getDefaults.getColor("Panel.background")
      new Color(c.getRed, c.getGreen, c.getBlue, c.getAlpha)
    }
    listenTo(mouse.clicks)
    listenTo(mouse.moves)
    reactions += {
      case MouseClicked(_, point, _, clicks, _) =>
        val index = peer.locationToIndex(point)
        if (index >= 0) {
          val index_location = peer.indexToLocation(index)
          val a = in_required(index_location, point)
          val b = in_required(index_location, point, document = true)
          if (a || b) {
            if (clicks == 1) {
              Document_Model.node_required(listData(index), toggle = true, document = b)
            }
          }
          else if (clicks == 2) PIDE.editor.goto_file(true, view, listData(index).node)
        }
      case MouseMoved(_, point, _) =>
        val index = peer.locationToIndex(point)
        val index_location = peer.indexToLocation(index)
        if (index >= 0 && in_required(index_location, point)) {
          tooltip = "Mark as required for continuous checking"
        }
        else if (index >= 0 && in_required(index_location, point, document = true)) {
          tooltip = "Mark as required for continuous checking, with inclusion in document"
        }
        else if (index >= 0 && in_label(index_location, point)) {
          val name = listData(index)
          val st = nodes_status.overall_node_status(name)
          tooltip =
            "theory " + quote(name.theory) +
              (if (st == Document_Status.Overall_Node_Status.ok) "" else " (" + st + ")")
        }
        else tooltip = null
    }
  }

  gui.renderer = new Node_Renderer
  gui.peer.setLayoutOrientation(JList.HORIZONTAL_WRAP)
  gui.peer.setVisibleRowCount(0)
  gui.selection.intervalMode = ListView.IntervalMode.Single


  /* update */

  def update(domain: Option[Set[Document.Node.Name]] = None, trim: Boolean = false): Unit = {
    GUI_Thread.require {}

    val snapshot = PIDE.session.snapshot()

    val (nodes_status_changed, nodes_status1) =
      nodes_status.update(
        PIDE.resources, snapshot.state, snapshot.version, domain = domain, trim = trim)

    nodes_status = nodes_status1
    if (nodes_status_changed) {
      gui.listData =
        (for {
          (name, node_status) <- nodes_status1.present.iterator
          if !node_status.is_suppressed && node_status.total > 0
        } yield name).toList
    }
  }


  /* reinit */

  def reinit(): Unit = {
    GUI_Thread.require {}

    theory_required = Document_Model.required_nodes(false)
    document_required = Document_Model.required_nodes(true)
    gui.repaint()
  }
}
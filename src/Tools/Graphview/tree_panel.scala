/*  Title:      Tools/Graphview/tree_panel.scala
    Author:     Makarius

Tree view on graph nodes.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Dimension, Rectangle}
import java.awt.event.{KeyEvent, KeyAdapter, MouseEvent, MouseAdapter}
import javax.swing.JTree
import javax.swing.tree.{DefaultMutableTreeNode, TreeSelectionModel, TreePath}
import javax.swing.event.{TreeSelectionEvent, TreeSelectionListener, DocumentListener, DocumentEvent}

import scala.util.matching.Regex
import scala.swing.{Component, ScrollPane, BorderPanel, Label, TextField, Button, CheckBox, Action}


class Tree_Panel(val visualizer: Visualizer, graph_panel: Graph_Panel) extends BorderPanel
{
  /* main actions */

  private def selection_action()
  {
    if (tree != null) {
      visualizer.current_node = None
      visualizer.Selection.clear()
      val paths = tree.getSelectionPaths
      if (paths != null) {
        for (path <- paths if path != null) {
          path.getLastPathComponent match {
            case tree_node: DefaultMutableTreeNode =>
              tree_node.getUserObject match {
                case node: Graph_Display.Node => visualizer.Selection.add(node)
                case _ =>
              }
            case _ =>
          }
        }
      }
      graph_panel.repaint()
    }
  }

  private def point_action(path: TreePath)
  {
    if (tree_pane != null && path != null) {
      val action_node =
        path.getLastPathComponent match {
          case tree_node: DefaultMutableTreeNode =>
            tree_node.getUserObject match {
              case node: Graph_Display.Node => Some(node)
              case _ => None
            }
          case _ => None
        }
      action_node.foreach(graph_panel.scroll_to_node(_))
      visualizer.current_node = action_node
      graph_panel.repaint()
    }
  }


  /* tree */

  private var nodes = List.empty[Graph_Display.Node]
  private val root = new DefaultMutableTreeNode("Nodes")

  val tree = new JTree(root)

  tree.addKeyListener(new KeyAdapter {
    override def keyPressed(e: KeyEvent): Unit =
      if (e.getKeyCode == KeyEvent.VK_ENTER) {
        e.consume
        selection_action()
      }
  })
  tree.addMouseListener(new MouseAdapter {
    override def mousePressed(e: MouseEvent): Unit =
      if (e.getClickCount == 2)
        point_action(tree.getPathForLocation(e.getX, e.getY))
  })

  private val tree_pane = new ScrollPane(Component.wrap(tree))
  tree_pane.horizontalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.verticalScrollBarPolicy = ScrollPane.BarPolicy.Always
  tree_pane.minimumSize = new Dimension(100, 50)
  tree_pane.peer.getVerticalScrollBar.setUnitIncrement(10)


  /* controls */

  private var selection_pattern: Option[Regex] = None

  private def selection_filter(node: Graph_Display.Node): Boolean =
    selection_pattern match {
      case None => false
      case Some(re) => re.pattern.matcher(node.toString).find
    }

  private val selection_label = new Label("Selection:") {
    tooltip = "Selection of nodes via regular expression"
  }

  private val selection_field = new TextField(10) {
    tooltip = selection_label.tooltip
  }
  private val selection_field_foreground = selection_field.foreground

  private val selection_delay =
    GUI_Thread.delay_last(visualizer.options.seconds("editor_input_delay")) {
      val (pattern, ok) =
        selection_field.text match {
          case null | "" => (None, true)
          case s =>
            val pattern = Library.make_regex(s)
            (pattern, pattern.isDefined)
        }
      if (selection_pattern != pattern) {
        selection_pattern = pattern
        tree.setSelectionRows(
          (for { (node, i) <- nodes.iterator.zipWithIndex if selection_filter(node) }
            yield i + 1).toArray)
        tree.repaint()
      }
      selection_field.foreground =
        if (ok) selection_field_foreground else visualizer.error_color
    }

  selection_field.peer.getDocument.addDocumentListener(new DocumentListener {
    def changedUpdate(e: DocumentEvent) { selection_delay.invoke() }
    def insertUpdate(e: DocumentEvent) { selection_delay.invoke() }
    def removeUpdate(e: DocumentEvent) { selection_delay.invoke() }
  })

  private val selection_apply = new Button {
    tooltip = "Apply tree selection to graph"
    action = Action("<html><b>Apply</b></html>") { selection_action () }
  }

  private val controls = new Wrap_Panel(Wrap_Panel.Alignment.Right)(
    selection_label, selection_field, selection_apply)


  /* main layout */

  def refresh()
  {
    val new_nodes = visualizer.visible_graph.topological_order
    if (new_nodes != nodes) {
      nodes = new_nodes

      root.removeAllChildren
      for (node <- nodes) root.add(new DefaultMutableTreeNode(node))

      tree.clearSelection
      for (i <- 0 until tree.getRowCount) tree.expandRow(i)
      tree.revalidate()
    }
    revalidate()
    repaint()
  }

  layout(tree_pane) = BorderPanel.Position.Center
  layout(controls) = BorderPanel.Position.North
  refresh()
}

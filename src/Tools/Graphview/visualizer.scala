/*  Title:      Tools/Graphview/visualizer.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graph visualization parameters and GUI state.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Font, Color, Shape, Graphics2D}
import java.awt.geom.{Point2D, Rectangle2D}
import javax.swing.JComponent


abstract class Visualizer(val model: Model)
{
  visualizer =>


  def options: Options


  /* layout state */

  // owned by GUI thread
  private var _layout: Layout = Layout.empty
  def layout: Layout = _layout

  def metrics: Metrics = layout.metrics
  def visible_graph: Graph_Display.Graph = layout.input_graph

  def translate_vertex(v: Layout.Vertex, dx: Double, dy: Double): Unit =
    _layout = _layout.translate_vertex(v, dx, dy)

  def find_node(at: Point2D): Option[Graph_Display.Node] =
    layout.output_graph.iterator.collectFirst({
      case (Layout.Node(node), (info, _)) if Shapes.shape(info).contains(at) => node
    })

  def find_dummy(at: Point2D): Option[Layout.Dummy] =
    layout.output_graph.iterator.collectFirst({
      case (dummy: Layout.Dummy, (info, _)) if Shapes.shape(info).contains(at) => dummy
    })

  def bounding_box(): Rectangle2D.Double =
  {
    var x0 = 0.0
    var y0 = 0.0
    var x1 = 0.0
    var y1 = 0.0
    for ((_, (info, _)) <- layout.output_graph.iterator) {
      val rect = Shapes.shape(info)
      x0 = x0 min rect.getMinX
      y0 = y0 min rect.getMinY
      x1 = x1 max rect.getMaxX
      y1 = y1 max rect.getMaxY
    }
    x0 = (x0 - metrics.gap).floor
    y0 = (y0 - metrics.gap).floor
    x1 = (x1 + metrics.gap).ceil
    y1 = (y1 + metrics.gap).ceil
    new Rectangle2D.Double(x0, y0, x1 - x0, y1 - y0)
  }

  def update_layout()
  {
    val metrics = Metrics(make_font())
    val visible_graph = model.make_visible_graph()

    def node_text(node: Graph_Display.Node, content: XML.Body): String =
      if (show_content) {
        val s =
          XML.content(Pretty.formatted(
            content, options.int("graphview_content_margin").toDouble, metrics.Pretty_Metric))
        if (s.nonEmpty) s else node.toString
      }
      else node.toString

    _layout = Layout.make(options, metrics, node_text _, visible_graph)
  }


  /* tooltips */

  def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String = null


  /* main colors */

  def foreground_color: Color = Color.BLACK
  def background_color: Color = Color.WHITE
  def selection_color: Color = Color.GREEN
  def current_color: Color = Color.YELLOW
  def error_color: Color = Color.RED
  def dummy_color: Color = Color.GRAY


  /* font rendering information */

  def make_font(): Font =
  {
    val family = options.string("graphview_font_family")
    val size = options.int("graphview_font_size")
    new Font(family, Font.PLAIN, size)
  }


  /* rendering parameters */

  // owned by GUI thread
  var show_content = false
  var show_arrow_heads = false
  var show_dummies = false

  object Colors
  {
    private val filter_colors = List(
      new Color(0xD9, 0xF2, 0xE2), // blue
      new Color(0xFF, 0xE7, 0xD8), // orange
      new Color(0xFF, 0xFF, 0xE5), // yellow
      new Color(0xDE, 0xCE, 0xFF), // lilac
      new Color(0xCC, 0xEB, 0xFF), // turquoise
      new Color(0xFF, 0xE5, 0xE5), // red
      new Color(0xE5, 0xE5, 0xD9)  // green
    )

    private var curr : Int = -1
    def next(): Color =
    {
      curr = (curr + 1) % filter_colors.length
      filter_colors(curr)
    }
  }

  def paint_all_visible(gfx: Graphics2D)
  {
    gfx.setRenderingHints(Metrics.rendering_hints)
    for (edge <- visible_graph.edges_iterator)
      Shapes.Cardinal_Spline_Edge.paint(gfx, visualizer, edge)
    for (node <- visible_graph.keys_iterator)
      Shapes.paint_node(gfx, visualizer, node)
  }

  var current_node: Option[Graph_Display.Node] = None

  object Selection
  {
    // owned by GUI thread
    private var state: List[Graph_Display.Node] = Nil

    def get(): List[Graph_Display.Node] = GUI_Thread.require { state }
    def contains(node: Graph_Display.Node): Boolean = get().contains(node)

    def add(node: Graph_Display.Node): Unit = GUI_Thread.require { state = node :: state }
    def clear(): Unit = GUI_Thread.require { state = Nil }
  }

  sealed case class Node_Color(border: Color, background: Color, foreground: Color)

  def node_color(node: Graph_Display.Node): Node_Color =
    if (current_node == Some(node))
      Node_Color(foreground_color, current_color, foreground_color)
    else if (Selection.contains(node))
      Node_Color(foreground_color, selection_color, foreground_color)
    else
      Node_Color(foreground_color, model.colors.getOrElse(node, background_color), foreground_color)

  def edge_color(edge: Graph_Display.Edge): Color = foreground_color
}
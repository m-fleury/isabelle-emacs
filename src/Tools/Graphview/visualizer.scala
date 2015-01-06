/*  Title:      Tools/Graphview/visualizer.scala
    Author:     Markus Kaiser, TU Muenchen
    Author:     Makarius

Graph visualization parameters and interface state.
*/

package isabelle.graphview


import isabelle._

import java.awt.{Font, Color, Shape, Graphics2D}
import java.awt.geom.Rectangle2D
import javax.swing.JComponent


class Visualizer(options: => Options, val model: Model)
{
  visualizer =>


  /* layout state */

  // owned by GUI thread
  private var _layout: Layout = Layout.empty
  def layout: Layout = _layout

  def metrics: Metrics = layout.metrics
  def visible_graph: Graph_Display.Graph = layout.input_graph

  def translate_vertex(v: Layout.Vertex, dx: Double, dy: Double): Unit =
    _layout = _layout.translate_vertex(v, dx, dy)

  def bounding_box(): Rectangle2D.Double =
  {
    var x0 = 0.0
    var y0 = 0.0
    var x1 = 0.0
    var y1 = 0.0
    ((for (node <- visible_graph.keys_iterator) yield Shapes.Node.shape(visualizer, node)) ++
     (for (d <- layout.dummies_iterator) yield Shapes.Dummy.shape(visualizer, d))).
       foreach(rect => {
          x0 = x0 min rect.getMinX
          y0 = y0 min rect.getMinY
          x1 = x1 max rect.getMaxX
          y1 = y1 max rect.getMaxY
        })
    val gap = metrics.gap
    x0 = (x0 - gap).floor
    y0 = (y0 - gap).floor
    x1 = (x1 + gap).ceil
    y1 = (y1 + gap).ceil
    new Rectangle2D.Double(x0, y0, x1 - x0, y1 - y0)
  }

  def update_layout()
  {
    val metrics = Metrics(make_font())
    val visible_graph = model.make_visible_graph()

    // FIXME avoid expensive operation on GUI thread
    _layout = Layout.make(metrics, visible_graph)
  }


  /* tooltips */

  def make_tooltip(parent: JComponent, x: Int, y: Int, body: XML.Body): String = null


  /* main colors */

  def foreground_color: Color = Color.BLACK
  def background_color: Color = Color.WHITE
  def selection_color: Color = Color.GREEN
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
  var arrow_heads = false
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
      Shapes.Node.paint(gfx, visualizer, node)
  }

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
    if (Selection.contains(node))
      Node_Color(foreground_color, selection_color, foreground_color)
    else
      Node_Color(foreground_color, model.colors.getOrElse(node, background_color), foreground_color)

  def edge_color(edge: Graph_Display.Edge): Color = foreground_color
}
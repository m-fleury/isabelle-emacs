/*  Title:      Pure/GUI/wrap_panel.scala
    Author:     Makarius

Panel with improved FlowLayout for wrapping of components over
multiple lines, see also
https://tips4java.wordpress.com/2008/11/06/wrap-layout/ and
scala.swing.FlowPanel.
*/

package isabelle


import java.awt.{FlowLayout, Container, Dimension}
import javax.swing.{JComponent, JPanel, JScrollPane}

import scala.swing.{Panel, FlowPanel, Component, SequentialContainer, ScrollPane}


object Wrap_Panel {
  val Alignment = FlowPanel.Alignment

  class Layout(align: Int = FlowLayout.CENTER, hgap: Int = 5, vgap: Int = 5)
      extends FlowLayout(align: Int, hgap: Int, vgap: Int) {
    override def preferredLayoutSize(target: Container): Dimension =
      layout_size(target, true)

    override def minimumLayoutSize(target: Container): Dimension = {
      val minimum = layout_size(target, false)
      minimum.width -= (getHgap + 1)
      minimum
    }

    private def layout_size(target: Container, preferred: Boolean): Dimension = {
      target.getTreeLock.synchronized {
        val target_width =
          if (target.getSize.width == 0) Int.MaxValue
          else target.getSize.width

        val hgap = getHgap
        val vgap = getVgap
        val insets = target.getInsets
        val horizontal_insets_and_gap = insets.left + insets.right + (hgap * 2)
        val max_width = target_width - horizontal_insets_and_gap


        /* fit components into rows */

        val dim = new Dimension(0, 0)
        var row_width = 0
        var row_height = 0
        def add_row(): Unit = {
          dim.width = dim.width max row_width
          if (dim.height > 0) dim.height += vgap
          dim.height += row_height
        }

        for {
          i <- (0 until target.getComponentCount).iterator
          m = target.getComponent(i)
          if m.isVisible
          d = if (preferred) m.getPreferredSize else m.getMinimumSize()
        } {
          if (row_width + d.width > max_width) {
            add_row()
            row_width = 0
            row_height = 0
          }

          if (row_width != 0) row_width += hgap

          row_width += d.width
          row_height = row_height max d.height
        }
        add_row()

        dim.width += horizontal_insets_and_gap
        dim.height += insets.top + insets.bottom + vgap * 2


        /* special treatment for ScrollPane */

        val scroll_pane =
          GUI.ancestors(target).exists(
            {
              case _: JScrollPane => true
              case c: JComponent if Component.wrap(c).isInstanceOf[ScrollPane] => true
              case _ => false
            })
        if (scroll_pane && target.isValid)
          dim.width -= (hgap + 1)

        dim
      }
    }
  }

  def apply(contents: List[Component] = Nil,
      alignment: Alignment.Value = Alignment.Right): Wrap_Panel =
    new Wrap_Panel(contents, alignment)
}

class Wrap_Panel(
  contents0: List[Component] = Nil,
  alignment: Wrap_Panel.Alignment.Value = Wrap_Panel.Alignment.Right)
extends Panel with SequentialContainer.Wrapper {
  override lazy val peer: JPanel =
    new JPanel(new Wrap_Panel.Layout(alignment.id)) with SuperMixin

  contents ++= contents0

  private def layoutManager = peer.getLayout.asInstanceOf[Wrap_Panel.Layout]

  def vGap: Int = layoutManager.getVgap
  def vGap_=(n: Int): Unit = layoutManager.setVgap(n)
  def hGap: Int = layoutManager.getHgap
  def hGap_=(n: Int): Unit = layoutManager.setHgap(n)
}

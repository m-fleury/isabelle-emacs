/*  Title:      Pure/General/position.scala
    Author:     Makarius

Position properties.
*/

package isabelle


import java.io.{File => JFile}


object Position
{
  type T = Properties.T

  val none: T = Nil

  val Line = new Properties.Int(Markup.LINE)
  val Offset = new Properties.Int(Markup.OFFSET)
  val End_Offset = new Properties.Int(Markup.END_OFFSET)
  val File = new Properties.String(Markup.FILE)
  val Id = new Properties.Long(Markup.ID)
  val Id_String = new Properties.String(Markup.ID)

  val Def_Line = new Properties.Int(Markup.DEF_LINE)
  val Def_Offset = new Properties.Int(Markup.DEF_OFFSET)
  val Def_End_Offset = new Properties.Int(Markup.DEF_END_OFFSET)
  val Def_File = new Properties.String(Markup.DEF_FILE)
  val Def_Id = new Properties.Long(Markup.DEF_ID)

  object Line_File
  {
    def apply(line: Int, file: String): T =
      (if (line > 0) Line(line) else Nil) :::
      (if (file != "") File(file) else Nil)

    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Line(i), File(name)) => Some((i, name))
        case (_, File(name)) => Some((1, name))
        case _ => None
      }
  }

  object Def_Line_File
  {
    def unapply(pos: T): Option[(Int, String)] =
      (pos, pos) match {
        case (Def_Line(i), Def_File(name)) => Some((i, name))
        case (_, Def_File(name)) => Some((1, name))
        case _ => None
      }
  }

  object Range
  {
    def apply(range: Symbol.Range): T = Offset(range.start) ::: End_Offset(range.stop)
    def unapply(pos: T): Option[Symbol.Range] =
      (pos, pos) match {
        case (Offset(start), End_Offset(stop)) if start <= stop => Some(Text.Range(start, stop))
        case (Offset(start), _) => Some(Text.Range(start, start + 1))
        case _ => None
      }
  }

  object Item_Id
  {
    def unapply(pos: T): Option[(Long, Symbol.Range)] =
      pos match {
        case Id(id) =>
          val offset = Offset.unapply(pos) getOrElse 0
          val end_offset = End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((id, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Item_Def_Id
  {
    def unapply(pos: T): Option[(Long, Symbol.Range)] =
      pos match {
        case Def_Id(id) =>
          val offset = Def_Offset.unapply(pos) getOrElse 0
          val end_offset = Def_End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((id, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Item_File
  {
    def unapply(pos: T): Option[(String, Int, Symbol.Range)] =
      pos match {
        case Line_File(line, name) =>
          val offset = Offset.unapply(pos) getOrElse 0
          val end_offset = End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((name, line, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Item_Def_File
  {
    def unapply(pos: T): Option[(String, Int, Symbol.Range)] =
      pos match {
        case Def_Line_File(line, name) =>
          val offset = Def_Offset.unapply(pos) getOrElse 0
          val end_offset = Def_End_Offset.unapply(pos) getOrElse (offset + 1)
          Some((name, line, Text.Range(offset, end_offset)))
        case _ => None
      }
  }

  object Identified
  {
    def unapply(pos: T): Option[(Long, Symbol.Text_Chunk.Name)] =
      pos match {
        case Id(id) =>
          val chunk_name =
            pos match {
              case File(name) => Symbol.Text_Chunk.File(name)
              case _ => Symbol.Text_Chunk.Default
            }
          Some((id, chunk_name))
        case _ => None
      }
  }

  def purge(props: T): T = props.filterNot(p => Markup.POSITION_PROPERTIES(p._1))


  /* here: user output */

  def here(pos: T): String =
    Markup(Markup.POSITION, pos).markup(
      (Line.unapply(pos), File.unapply(pos)) match {
        case (Some(i), None) => " (line " + i.toString + ")"
        case (Some(i), Some(name)) => " (line " + i.toString + " of " + quote(name) + ")"
        case (None, Some(name)) => " (file " + quote(name) + ")"
        case _ => ""
      })

  def here_undelimited(pos: T): String =
    Markup(Markup.POSITION, pos).markup(
      (Line.unapply(pos), File.unapply(pos)) match {
        case (Some(i), None) => "line " + i.toString
        case (Some(i), Some(name)) => "line " + i.toString + " of " + quote(name)
        case (None, Some(name)) => "file " + quote(name)
        case _ => ""
      })
}

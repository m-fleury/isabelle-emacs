/*  Title:      Pure/Tools/isabelle_fonts.scala
    Author:     Makarius

Construction of Isabelle fonts.
*/

package isabelle


object Isabelle_Fonts
{
  /* relevant codepoint ranges */

  object Range
  {
    def plain_text: Seq[Int] =
      (0x0020 to 0x007e) ++  // ASCII
      (0x00a0 to 0x024f) ++  // Latin Extended-A/B
      (0x0400 to 0x04ff) ++  // Cyrillic
      (0x0590 to 0x05ff) ++  // Hebrew (non-mono)
      (0x0600 to 0x06ff) ++  // Arabic
      Seq(
        0x2018,  // single quote
        0x2019,  // single quote
        0x201a,  // single quote
        0x201c,  // double quote
        0x201d,  // double quote
        0x201e,  // double quote
        0x2039,  // single guillemet
        0x203a,  // single guillemet
        0x204b,  // reversed pilcrow
        0x20ac,  // Euro
        0xfb01,  // ligature fi
        0xfb02,  // ligature fl
        0xfffd,  // replacement character
      )

    def symbols: Seq[Int] =
      Seq(
        0x05,  // X
        0x06,  // Y
        0x07,  // EOF
        0x7f,  // DEL
        0xac,  // logicalnot
        0xb0,  // degree
        0xb1,  // plusminus
        0xb7,  // periodcentered
        0xd7,  // multiply
        0xf7,  // divide
      ) ++
      (0x0370 to 0x03ff) ++  // Greek (pseudo math)
      Seq(
        0x2010,  // hyphen
        0x2013,  // dash
        0x2014,  // dash
        0x2015,  // dash
        0x2020,  // dagger
        0x2021,  // double dagger
        0x2022,  // bullet
        0x2026,  // ellipsis
        0x2030,  // perthousand
        0x2032,  // minute
        0x2033,  // second
        0x2038,  // caret
        0x20cd,  // currency symbol
      ) ++
      (0x2100 to 0x214f) ++  // Letterlike Symbols
      (0x2190 to 0x21ff) ++  // Arrows
      (0x2200 to 0x22ff) ++  // Mathematical Operators
      (0x2300 to 0x23ff) ++  // Miscellaneous Technical
      Seq(
        0x2423,  // graphic for space
        0x2500,  // box drawing
        0x2501,  // box drawing
        0x2508,  // box drawing
        0x2509,  // box drawing
        0x2550,  // box drawing
      ) ++
      (0x25a0 to 0x25ff) ++  // Geometric Shapes
      Seq(
        0x261b,  // black right pointing index
        0x2660,  // spade suit
        0x2661,  // heart suit
        0x2662,  // diamond suit
        0x2663,  // club suit
        0x266d,  // musical flat
        0x266e,  // musical natural
        0x266f,  // musical sharp
        0x2756,  // UNDEFINED
        0x2759,  // BOLD
        0x27a7,  // DESCR
        0x27e6,  // left white square bracket
        0x27e7,  // right white square bracket
        0x27e8,  // left angle bracket
        0x27e9,  // right angle bracket
      ) ++
      (0x27f0 to 0x27ff) ++  // Supplemental Arrows-A
      (0x2900 to 0x297f) ++  // Supplemental Arrows-B
      (0x2980 to 0x29ff) ++  // Miscellaneous Mathematical Symbols-B
      (0x2a00 to 0x2aff) ++  // Supplemental Mathematical Operators
      Seq(0x2b1a) ++  // VERBATIM
      (0x1d400 to 0x1d7ff) ++  // Mathematical Alphanumeric Symbols
      Seq(
        0x1f310,  // globe with meridians
        0x1f4d3,  // notebook
        0x1f5c0,  // folder
        0x1f5cf,  // page
      )
  }


  /* font families */

  sealed case class Family(plain: String, bold: String, italic: String, bold_italic: String)

  object Family
  {
    val deja_vu_sans_mono =
      Family(
        "DejaVuSansMono",
        "DejaVuSansMono-Bold",
        "DejaVuSansMono-Oblique",
        "DejaVuSansMono-BoldOblique")

    val deja_vu_sans =
      Family(
        "DejaVuSans",
        "DejaVuSans-Bold",
        "DejaVuSans-Oblique",
        "DejaVuSans-BoldOblique")

    val deja_vu_serif =
      Family(
        "DejaVuSerif",
        "DejaVuSerif-Bold",
        "DejaVuSerif-Italic",
        "DejaVuSerif-BoldItalic")
  }
}

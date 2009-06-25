/*
 * Isabelle encoding -- based on utf-8
 *
 * @author Makarius
 */

package isabelle.jedit

import org.gjt.sp.jedit.io.Encoding

import java.nio.charset.{Charset, CharsetDecoder, CodingErrorAction}
import java.io.{InputStream, OutputStream, Reader, Writer, InputStreamReader, OutputStreamWriter,
  CharArrayReader, ByteArrayOutputStream}

import scala.io.{Source, BufferedSource}


class IsabelleEncoding extends Encoding
{
  private val charset = Charset.forName(Isabelle_System.charset)
  private val BUFSIZE = 32768

  private def text_reader(in: InputStream, decoder: CharsetDecoder): Reader =
  {
    def source(): Source =
      BufferedSource.fromInputStream(in, decoder, BUFSIZE, { () => source() })
    val text = Source.fromInputStream(in, Isabelle_System.charset).mkString
    val buffer = Isabelle.symbols.decode(text).toArray
		new CharArrayReader(buffer)
  }

	override def getTextReader(in: InputStream): Reader =
    text_reader(in, charset.newDecoder())

	override def getPermissiveTextReader(in: InputStream): Reader =
	{
		val decoder = charset.newDecoder()
		decoder.onMalformedInput(CodingErrorAction.REPLACE)
		decoder.onUnmappableCharacter(CodingErrorAction.REPLACE)
		text_reader(in, decoder)
	}

  override def getTextWriter(out: OutputStream): Writer =
  {
    val buffer = new ByteArrayOutputStream(BUFSIZE) {
      override def flush()
      {
        val text = Isabelle.symbols.encode(toString(Isabelle_System.charset))
        out.write(text.getBytes(Isabelle_System.charset))
        out.flush()
      }
    }
		new OutputStreamWriter(buffer, charset.newEncoder())
  }
}

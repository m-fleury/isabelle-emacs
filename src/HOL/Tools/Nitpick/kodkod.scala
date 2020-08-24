/*  Title:      HOL/Tools/Nitpick/kodkod.scala
    Author:     Makarius

Scala interface for Kodkod.
*/

package isabelle.nitpick

import isabelle._

import java.util.concurrent.Executors

import org.antlr.runtime.{ANTLRInputStream, RecognitionException}
import de.tum.in.isabelle.Kodkodi.{Context, KodkodiLexer, KodkodiParser}


object Kodkod
{
  sealed case class Result(rc: Int, out: String, err: String)
  {
    def ok: Boolean = rc == 0
    def check: String =
      if (ok) out else error(if (err.isEmpty) "Error" else err)

    def encode: XML.Body =
    {
      import XML.Encode._
      triple(int, string, string)((rc, out, err))
    }
  }

  def execute(source: String,
    solve_all: Boolean = false,
    prove: Boolean = false,
    max_solutions: Int = Integer.MAX_VALUE,
    cleanup_inst: Boolean = false,
    timeout: Time = Time.zero,
    max_threads: Int = 0): Result =
  {
    val pool_size = if (max_threads == 0) Isabelle_Thread.max_threads() else max_threads
    val executor = Executors.newFixedThreadPool(pool_size)

    def executor_kill(): Unit =
      if (!executor.isShutdown) Isabelle_Thread.fork() { executor.shutdownNow() }

    class Exit extends Exception("EXIT")

    val context =
      new Context {
        private var rc = 0
        private val out = new StringBuilder
        private val err = new StringBuilder

        def return_code(i: Int): Unit = synchronized { rc = rc max i}
        override def output(s: String): Unit = synchronized { out ++= s; out += '\n' }
        override def error(s: String): Unit = synchronized { err ++= s; err += '\n' }
        override def exit(i: Int): Unit =
          synchronized {
            return_code(i)
            executor_kill()
            throw new Exit
          }

        def result(): Result = synchronized { Result(rc, out.toString, err.toString) }
      }

    try {
      val lexer = new KodkodiLexer(new ANTLRInputStream(Bytes(source).stream))
      val parser =
        KodkodiParser.create(context, executor,
          false, solve_all, prove, max_solutions, cleanup_inst, lexer)

      val timeout_request =
        if (timeout.is_zero) None
        else {
          Some(Event_Timer.request(Time.now() + timeout) {
            context.error("Ran out of time")
            context.return_code(2)
            executor_kill()
          })
        }

      try { parser.problems() }
      catch { case exn: RecognitionException => parser.reportError(exn) }

      timeout_request.foreach(_.cancel)

      if (parser.getTokenStream.LA(1) != KodkodiParser.EOF) {
        context.error("Error: trailing tokens")
        context.exit(1)
      }
      if (lexer.getNumberOfSyntaxErrors + parser.getNumberOfSyntaxErrors > 0) {
        context.exit(1)
      }
    }
    catch {
      case _: Exit =>
      case exn: Throwable =>
        val message = exn.getMessage
        context.error(if (message.isEmpty) exn.toString else "Error: " + message)
        context.return_code(1)
    }

    context.result()
  }

  def warmup(): String =
    execute(
      "solver: \"MiniSat\"\n" +
      File.read(Path.explode("$KODKODI/examples/weber3.kki"))).check


  /* scala function */

  object Fun extends Scala.Fun("kodkod")
  {
    def apply(args: String): String =
    {
      val (timeout, (solve_all, (max_solutions, (max_threads, kki)))) =
      {
        import XML.Decode._
        pair(int, pair(bool, pair(int, pair(int, string))))(YXML.parse_body(args))
      }
      val result =
        execute(kki,
          solve_all = solve_all,
          max_solutions = max_solutions,
          timeout = Time.ms(timeout),
          max_threads = max_threads)
      YXML.string_of_body(result.encode)
    }
  }
}

class Scala_Functions extends Scala.Functions(Kodkod.Fun)

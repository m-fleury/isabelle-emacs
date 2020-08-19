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

  def kodkod(source: String,
    solve_all: Boolean = false,
    prove: Boolean = false,
    max_solutions: Int = Integer.MAX_VALUE,
    cleanup_inst: Boolean = false,
    timeout: Time = Time.zero,
    max_threads: Int = 1): Result =
  {
    val executor = Executors.newFixedThreadPool(max_threads)

    def executor_kill(): Unit =
      if (!executor.isShutdown) Isabelle_Thread.fork() { executor.shutdownNow() }

    class Exit extends Exception

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
}

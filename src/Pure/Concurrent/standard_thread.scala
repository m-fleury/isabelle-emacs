/*  Title:      Pure/Concurrent/standard_thread.scala
    Author:     Makarius

Standard thread operations.
*/

package isabelle


import java.util.concurrent.{ThreadPoolExecutor, TimeUnit, LinkedBlockingQueue, ThreadFactory}


object Standard_Thread
{
  /* fork */

  private val counter = Counter.make()

  def make_name(name: String, base: String = "thread"): String =
    proper_string(name).getOrElse(base + counter())

  def fork(name: String = "", daemon: Boolean = false)(body: => Unit): Standard_Thread =
  {
    val group = Thread.currentThread.getThreadGroup
    val main = new Runnable { override def run { body } }
    val thread = new Standard_Thread(group, main, make_name(name), daemon)
    thread.start
    thread
  }


  /* self */

  def self: Option[Standard_Thread] =
    Thread.currentThread match {
      case thread: Standard_Thread => Some(thread)
      case _ => None
    }

  def uninterruptible[A](body: => A): A =
  {
    self match {
      case Some(thread) => thread.uninterruptible(body)
      case None => error("Cannot change interrupts --- running on non-standard thread")
    }
  }


  /* pool */

  lazy val pool: ThreadPoolExecutor =
    {
      val m = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0
      val n = if (m > 0) m else (Runtime.getRuntime.availableProcessors max 1) min 8
      val executor =
        new ThreadPoolExecutor(n, n, 2500L, TimeUnit.MILLISECONDS, new LinkedBlockingQueue[Runnable])
      val old_thread_factory = executor.getThreadFactory
      executor.setThreadFactory(
        new ThreadFactory {
          def newThread(r: Runnable) =
          {
            val thread = old_thread_factory.newThread(r)
            thread.setDaemon(true)
            thread
          }
        })
      executor
    }


  /* delayed events */

  final class Delay private[Standard_Thread](
    first: Boolean, delay: => Time, log: Logger, event: => Unit)
  {
    private var running: Option[Event_Timer.Request] = None

    private def run: Unit =
    {
      val do_run = synchronized {
        if (running.isDefined) { running = None; true } else false
      }
      if (do_run) {
        try { event }
        catch { case exn: Throwable if !Exn.is_interrupt(exn) => log(Exn.message(exn)); throw exn }
      }
    }

    def invoke(): Unit = synchronized
    {
      val new_run =
        running match {
          case Some(request) => if (first) false else { request.cancel; true }
          case None => true
        }
      if (new_run)
        running = Some(Event_Timer.request(Time.now() + delay)(run))
    }

    def revoke(): Unit = synchronized
    {
      running match {
        case Some(request) => request.cancel; running = None
        case None =>
      }
    }

    def postpone(alt_delay: Time): Unit = synchronized
    {
      running match {
        case Some(request) =>
          val alt_time = Time.now() + alt_delay
          if (request.time < alt_time && request.cancel) {
            running = Some(Event_Timer.request(alt_time)(run))
          }
        case None =>
      }
    }
  }

  // delayed event after first invocation
  def delay_first(delay: => Time, log: Logger = No_Logger)(event: => Unit): Delay =
    new Delay(true, delay, log, event)

  // delayed event after last invocation
  def delay_last(delay: => Time, log: Logger = No_Logger)(event: => Unit): Delay =
    new Delay(false, delay, log, event)
}

class Standard_Thread private(group: ThreadGroup, main: Runnable, name: String, daemon: Boolean)
  extends Thread(group, null, name)
{
  thread =>

  thread.setDaemon(daemon)

  override def run { main.run() }

  private var interruptible: Boolean = true
  private var interrupt_pending: Boolean = false

  override def interrupt: Unit = synchronized
  {
    if (interruptible) super.interrupt()
    else { interrupt_pending = true }
  }

  def uninterruptible[A](body: => A): A =
  {
    require(Thread.currentThread == thread)

    val interruptible0 = synchronized { val b = interruptible; interruptible = false; b }
    try { body }
    finally {
      synchronized {
        interruptible = interruptible0
        if (interruptible && interrupt_pending) {
          interrupt_pending = false
          super.interrupt()
        }
      }
    }
  }
}

/*  Title:      Pure/Concurrent/future.scala
    Author:     Makarius

Value-oriented parallel execution via futures and promises.
*/

package isabelle


import java.util.concurrent.Callable


/* futures and promises */

object Future {
  def value[A](x: A): Future[A] = new Value_Future(x)
  def fork[A](body: => A): Future[A] = new Task_Future[A](body)
  def promise[A]: Promise[A] = new Promise_Future[A]

  def thread[A](
    name: String = "",
    group: ThreadGroup = Isabelle_Thread.current_thread_group,
    pri: Int = Thread.NORM_PRIORITY,
    daemon: Boolean = false,
    inherit_locals: Boolean = false,
    uninterruptible: Boolean = false)(
    body: => A
  ): Future[A] = {
    new Thread_Future[A](name, group, pri, daemon, inherit_locals, uninterruptible, body)
  }
}

trait Future[A] {
  def peek: Option[Exn.Result[A]]
  def is_finished: Boolean = peek.isDefined
  def get_finished: A = { require(is_finished, "future not finished"); Exn.release(peek.get) }
  def join_result: Exn.Result[A]
  def join: A = Exn.release(join_result)
  def map[B](f: A => B): Future[B] = Future.fork { f(join) }
  def cancel(): Unit

  override def toString: String =
    peek match {
      case None => "<future>"
      case Some(Exn.Exn(_)) => "<failed>"
      case Some(Exn.Res(x)) => x.toString
    }
}

trait Promise[A] extends Future[A] {
  def fulfill_result(res: Exn.Result[A]): Unit
  def fulfill(x: A): Unit
}


/* value future */

private class Value_Future[A](x: A) extends Future[A] {
  val peek: Option[Exn.Result[A]] = Some(Exn.Res(x))
  def join_result: Exn.Result[A] = peek.get
  def cancel(): Unit = {}
}


/* task future via thread pool */

private class Task_Future[A](body: => A) extends Future[A] {
  private enum Status {
    case Ready extends Status
    case Running(thread: Thread) extends Status
    case Terminated extends Status
    case Finished(result: Exn.Result[A]) extends Status
  }

  private val status = Synchronized[Status](Status.Ready)

  def peek: Option[Exn.Result[A]] =
    status.value match {
      case Status.Finished(result) => Some(result)
      case _ => None
    }

  private def try_run(): Unit = {
    val do_run =
      status.change_result {
        case Status.Ready => (true, Status.Running(Thread.currentThread))
        case st => (false, st)
      }
    if (do_run) {
      val result = Exn.capture(body)
      status.change(_ => Status.Terminated)
      status.change(_ =>
        Status.Finished(if (Thread.interrupted()) Exn.Exn(Exn.Interrupt()) else result))
    }
  }
  private val task = Isabelle_Thread.pool.submit(new Callable[Unit] { def call = try_run() })

  def join_result: Exn.Result[A] = {
    try_run()
    status.guarded_access {
      case st @ Status.Finished(result) => Some((result, st))
      case _ => None
    }
  }

  def cancel(): Unit = {
    status.change {
      case Status.Ready => task.cancel(false); Status.Finished(Exn.Exn(Exn.Interrupt()))
      case st @ Status.Running(thread) => thread.interrupt(); st
      case st => st
    }
  }
}


/* promise future */

private class Promise_Future[A] extends Promise[A] {
  private val state = Synchronized[Option[Exn.Result[A]]](None)
  def peek: Option[Exn.Result[A]] = state.value

  def join_result: Exn.Result[A] =
    state.guarded_access(st => if (st.isEmpty) None else Some((st.get, st)))

  def fulfill_result(result: Exn.Result[A]): Unit =
    state.change(st => if (st.isEmpty) Some(result) else throw new IllegalStateException)

  def fulfill(x: A): Unit = fulfill_result(Exn.Res(x))

  def cancel(): Unit =
    state.change(st => if (st.isEmpty) Some(Exn.Exn(Exn.Interrupt())) else st)
}


/* thread future */

private class Thread_Future[A](
  name: String,
  group: ThreadGroup,
  pri: Int,
  daemon: Boolean,
  inherit_locals: Boolean,
  uninterruptible: Boolean,
  body: => A
) extends Future[A] {
  private val result = Future.promise[A]
  private val thread =
    Isabelle_Thread.fork(name = name, group = group, pri = pri, daemon = daemon,
      inherit_locals = inherit_locals, uninterruptible = uninterruptible) {
      result.fulfill_result(Exn.capture(body)) }

  def peek: Option[Exn.Result[A]] = result.peek
  def join_result: Exn.Result[A] = result.join_result
  def cancel(): Unit = thread.interrupt()
}

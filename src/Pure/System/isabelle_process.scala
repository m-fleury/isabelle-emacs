/*  Title:      Pure/System/isabelle_process.scala
    Author:     Makarius

Isabelle process wrapper.
*/

package isabelle


object Isabelle_Process
{
  def apply(
    options: Options,
    heap: String = "",
    args: List[String] = Nil,
    modes: List[String] = Nil,
    secure: Boolean = false,
    receiver: Prover.Receiver = Console.println(_)): Isabelle_Process =
  {
    val channel = System_Channel()
    val process =
      try {
        ML_Process(options, heap = heap, args = args, modes = modes, secure = secure,
          channel = Some(channel))
      }
      catch { case exn @ ERROR(_) => channel.accepted(); throw exn }
    process.stdin.close

    new Isabelle_Process(receiver, channel, process)
  }
}

class Isabelle_Process private(
    receiver: Prover.Receiver, channel: System_Channel, process: Prover.System_Process)
  extends Prover(receiver, channel, process)
{
  def encode(s: String): String = Symbol.encode(s)
  def decode(s: String): String = Symbol.decode(s)
}

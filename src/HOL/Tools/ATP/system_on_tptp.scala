/*  Title:      HOL/Tools/ATP/system_on_tptp.scala
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*/

package isabelle.atp

import isabelle._


object SystemOnTPTP {
  /* requests */

  def get_url(options: Options): Url = Url(options.string("SystemOnTPTP"))

  def post_request(
    url: Url,
    parameters: List[(String, Any)],
    timeout: Time = HTTP.Client.default_timeout
  ): HTTP.Content = {
    try {
      HTTP.Client.post(url,
        ("NoHTML" -> 1) :: parameters,
        timeout = timeout,
        user_agent = "Sledgehammer")
    }
    catch { case ERROR(msg) => cat_error("Failed to access SystemOnTPTP server", msg) }
  }


  /* list systems */

  def list_systems(url: Url): HTTP.Content =
    post_request(url,
      List("SubmitButton" -> "ListSystems",
        "ListStatus" -> "READY",
        "QuietFlag" -> "-q0"))

  object List_Systems extends Scala.Fun_String("SystemOnTPTP.list_systems", thread = true) {
    val here = Scala_Project.here
    def apply(url: String): String = list_systems(Url(url)).text
  }


  /* run system */

  def run_system(url: Url,
    system: String,
    problem: String,
    extra: String = "",
    quiet: String = "01",
    timeout: Time = Time.seconds(60)
  ): HTTP.Content = {
    val paramaters =
      List(
        "SubmitButton" -> "RunSelectedSystems",
        "ProblemSource" -> "FORMULAE",
        "FORMULAEProblem" -> problem,
        "ForceSystem" -> "-force",
        "System___" + system -> system,
        "TimeLimit___" + system -> timeout.seconds.ceil.toLong,
        "Command___" + system -> extra,
        "QuietFlag" -> ("-q" + quiet))
    post_request(url, paramaters, timeout = timeout + Time.seconds(15))
  }

  object Run_System extends Scala.Fun_Strings("SystemOnTPTP.run_system", thread = true) {
    val here = Scala_Project.here
    def apply(args: List[String]): List[String] = {
      val List(url, system, problem_path, extra, Value.Int(timeout)) = args : @unchecked
      val problem = File.read(Path.explode(problem_path))

      val res = run_system(Url(url), system, problem, extra = extra, timeout = Time.ms(timeout))
      val text = res.text
      val timing = res.elapsed_time.ms

      val bad_prover = "WARNING: " + system + " does not exist"
      if (split_lines(text).exists(_.startsWith(bad_prover))) {
        error("The ATP " + quote(system) + " is not available at SystemOnTPTP")
      }
      else List(text, timing.toString)
    }
  }
}

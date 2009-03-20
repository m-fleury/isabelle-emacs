/*
 * Document as list of commands, consisting of lists of tokens
 *
 * @author Johannes Hölzl, TU Munich
 * @author Fabian Immler, TU Munich
 * @author Makarius
 */

package isabelle.proofdocument

import scala.collection.mutable.ListBuffer
import scala.actors.Actor
import scala.actors.Actor._
import java.util.regex.Pattern
import isabelle.prover.{Prover, Command}
import isabelle.utils.LinearSet

case class StructureChange(
  val before_change: Option[Command],
  val added_commands: List[Command],
  val removed_commands: List[Command])

object ProofDocument
{
  // Be carefully when changing this regex. Not only must it handle the 
  // spurious end of a token but also:  
  // Bug ID: 5050507 Pattern.matches throws StackOverflow Error
  // http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=5050507
  
  val token_pattern = 
    Pattern.compile(
      "\\{\\*([^*]|\\*[^}]|\\*\\z)*(\\z|\\*\\})|" +
      "\\(\\*([^*]|\\*[^)]|\\*\\z)*(\\z|\\*\\))|" +
      "(\\?'?|')[A-Za-z_0-9.]*|" + 
      "[A-Za-z_0-9.]+|" + 
      "[!#$%&*+-/<=>?@^_|~]+|" +
      "\"([^\\\\\"]?(\\\\(.|\\z))?)*+(\"|\\z)|" +
      "`([^\\\\`]?(\\\\(.|\\z))?)*+(`|\\z)|" +
      "[()\\[\\]{}:;]", Pattern.MULTILINE)

 val empty = new ProofDocument(LinearSet.empty, LinearSet.empty, false, _ => false)

}

class ProofDocument(val tokens: LinearSet[Token],
                    val commands: LinearSet[Command],
                    val active: Boolean,
                    is_command_keyword: String => Boolean)
{

  def mark_active: ProofDocument = new ProofDocument(tokens, commands, true, is_command_keyword)
  def activate: (ProofDocument, StructureChange) = {
    val (doc, change) = text_changed(new Text.Change(0, 0, content, content.length))
    return (doc.mark_active, change)
  }
  def set_command_keyword(f: String => Boolean): ProofDocument =
    new ProofDocument(tokens, commands, active, f)

  def content = Token.string_from_tokens(List() ++ tokens)
  /** token view **/

  def text_changed(change: Text.Change): (ProofDocument, StructureChange) =
  {
    val tokens = List() ++ this.tokens
    val (begin, remaining) = tokens.span(_.stop < change.start)
    val (removed, end_unshifted) = remaining.span(_.start <= change.start + change.removed)
    val end = for (t <- end_unshifted) yield t.shift(change.added.length - change.removed)

    val split_begin = removed.takeWhile(_.start < change.start).
      map (t => new Token(t.start,
                          t.content.substring(0, change.start - t.start),
                          t.kind))
    val split_end = removed.dropWhile(_.stop < change.start + change.removed).
      map (t => new Token(change.start + change.added.length,
                          t.content.substring(change.start + change.removed - t.start),
                          t.kind))

    var invalid_tokens =  split_begin :::
      new Token(change.start, change.added, Token.Kind.OTHER) :: split_end ::: end
    var new_tokens = Nil: List[Token]
    var old_suffix = Nil: List[Token]

    val match_start = invalid_tokens.first.start
    val matcher = ProofDocument.token_pattern.matcher(Token.string_from_tokens(invalid_tokens))

    while (matcher.find() && invalid_tokens != Nil) {
			val kind =
        if (is_command_keyword(matcher.group))
          Token.Kind.COMMAND_START
        else if (matcher.end - matcher.start > 2 && matcher.group.substring(0, 2) == "(*")
          Token.Kind.COMMENT
        else
          Token.Kind.OTHER
      val new_token = new Token(match_start + matcher.start, matcher.group, kind)
      new_tokens ::= new_token

      invalid_tokens = invalid_tokens dropWhile (_.stop < new_token.stop)
      invalid_tokens match {
        case t::ts => if(t.start == new_token.start &&
                         t.start > change.start + change.added.length) {
          old_suffix = ts
          invalid_tokens = Nil
        }
        case _ =>
      }
    }
    val insert = new_tokens.reverse
    val new_tokenset = (new LinearSet() ++ (begin ::: insert ::: old_suffix)).asInstanceOf[LinearSet[Token]]

    token_changed(begin.lastOption,
                  insert,
                  removed,
                  new_tokenset,
                  old_suffix.firstOption)
  }
  
  /** command view **/

  def find_command_at(pos: Int): Command = {
    for (cmd <- commands) { if (pos < cmd.stop) return cmd }
    return null
  }

  private def token_changed(before_change: Option[Token],
                            inserted_tokens: List[Token],
                            removed_tokens: List[Token],
                            new_tokenset: LinearSet[Token],
                            after_change: Option[Token]): (ProofDocument, StructureChange) =
  {
    val commands = List() ++ this.commands
    val (begin, remaining) =
      before_change match {
        case None => (Nil, commands)
        case Some(bc) => commands.break(_.tokens.contains(bc))
      }
    val (_removed, _end) =
      after_change match {
        case None => (remaining, Nil)
        case Some(ac) => remaining.break(_.tokens.contains(ac))
      }
    val (removed, end) = _end match {
      case Nil => (_removed, Nil)
      case acc::end => if (after_change.isDefined && after_change.get.kind == Token.Kind.COMMAND_START)
          (_removed, _end)
        else (_removed ::: List(acc), end)
    }
    val all_removed_tokens = for(c <- removed; t <- c.tokens) yield t
    val (pseudo_new_pre, rest) =
      if (! before_change.isDefined) (Nil, all_removed_tokens)
      else {
        val (a, b) = all_removed_tokens.span (_ != before_change.get)
        b match {
          case Nil => (a, Nil)
          case bc::rest => (a ::: List(bc), b)
        }
      }
    val pseudo_new_post = rest.dropWhile(Some(_) != after_change)

    def tokens_to_commands(tokens: List[Token]): List[Command]= {
      tokens match {
        case Nil => Nil
        case t::ts =>
          val (cmd,rest) = ts.span(_.kind != Token.Kind.COMMAND_START)
          new Command(t::cmd) :: tokens_to_commands (rest)
      }
    }

    val new_commands = tokens_to_commands(pseudo_new_pre ::: inserted_tokens ::: pseudo_new_post)

    val new_commandset = (LinearSet() ++ (begin ::: new_commands ::: end)).asInstanceOf[LinearSet[Command]]
    val before = begin match {case Nil => None case _ => Some (begin.last)}

    val change = new StructureChange(before, new_commands, removed)
    val doc = new ProofDocument(new_tokenset, new_commandset, active, is_command_keyword)
    return (doc, change)
  }
}

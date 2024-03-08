/*  Title:      Pure/General/date.scala
    Author:     Makarius

Date and time, with time zone.
*/

package isabelle


import java.util.Locale
import java.time.{Instant, ZonedDateTime, LocalTime, ZoneId}
import java.time.format.{DateTimeFormatter, DateTimeParseException}
import java.time.temporal.TemporalAccessor

import scala.annotation.tailrec


object Date {
  /* format */

  object Format {
    def make(fmts: List[DateTimeFormatter], tune: String => String = s => s): Format = {
      require(fmts.nonEmpty, "no date formats")

      new Format {
        def apply(date: Date): String = fmts.head.format(date.rep)
        def parse(str: String): Date =
          new Date(ZonedDateTime.from(Formatter.try_variants(fmts, tune(str))))
      }
    }

    def apply(pats: String*): Format =
      make(pats.toList.map(Date.Formatter.pattern))

    val default: Format = Format("dd-MMM-uuuu HH:mm:ss xx")
    val date: Format = Format("dd-MMM-uuuu")
    val time: Format = Format("HH:mm:ss")
    val alt_date: Format = Format("uuuuMMdd")
  }

  abstract class Format private {
    def apply(date: Date): String
    def parse(str: String): Date

    def unapply(str: String): Option[Date] =
      try { Some(parse(str)) } catch { case _: DateTimeParseException => None }
  }

  object Formatter {
    def pattern(pat: String): DateTimeFormatter = DateTimeFormatter.ofPattern(pat)

    def variants(pats: List[String], locs: List[Locale] = Nil): List[DateTimeFormatter] =
      pats.flatMap { pat =>
        val fmt = pattern(pat)
        if (locs.isEmpty) List(fmt) else locs.map(fmt.withLocale)
      }

    @tailrec def try_variants(
      fmts: List[DateTimeFormatter],
      str: String,
      last_exn: Option[DateTimeParseException] = None
    ): TemporalAccessor = {
      fmts match {
        case Nil =>
          throw last_exn.getOrElse(new DateTimeParseException("Failed to parse date", str, 0))
        case fmt :: rest =>
          try { ZonedDateTime.from(fmt.parse(str)) }
          catch { case exn: DateTimeParseException => try_variants(rest, str, Some(exn)) }
      }
    }
  }


  /* ordering */

  object Ordering extends scala.math.Ordering[Date] {
    def compare(date1: Date, date2: Date): Int =
      date1.instant.compareTo(date2.instant)
  }

  object Rev_Ordering extends scala.math.Ordering[Date] {
    def compare(date1: Date, date2: Date): Int =
      date2.instant.compareTo(date1.instant)
  }


  /* date operations */

  def timezone_utc: ZoneId = ZoneId.of("UTC")
  def timezone_berlin: ZoneId = ZoneId.of("Europe/Berlin")

  def timezone(): ZoneId = ZoneId.systemDefault

  def now(zone: ZoneId = timezone()): Date = new Date(ZonedDateTime.now(zone))

  def instant(t: Instant, zone: ZoneId = timezone()): Date =
    new Date(ZonedDateTime.ofInstant(t, zone))

  def apply(t: Time, zone: ZoneId = timezone()): Date = instant(t.instant, zone)
}

sealed case class Date(rep: ZonedDateTime) {
  def midnight: Date =
    new Date(ZonedDateTime.of(rep.toLocalDate, LocalTime.MIDNIGHT, rep.getZone))

  def to(zone: ZoneId): Date = new Date(rep.withZoneSameInstant(zone))

  def unix_epoch: Long = rep.toEpochSecond
  def unix_epoch_day: Long = rep.toLocalDate.toEpochDay
  def instant: Instant = Instant.from(rep)
  def time: Time = Time.instant(instant)
  def timezone: ZoneId = rep.getZone

  def + (t: Time): Date = Date(time + t, zone = timezone)
  def - (t: Time): Date = Date(time - t, zone = timezone)
  def - (d: Date): Time = time - d.time

  def format(fmt: Date.Format = Date.Format.default): String = fmt(this)
  override def toString: String = format()
}

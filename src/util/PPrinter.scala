package scala.virtualization.lms
package util

/**
 * Pretty printer for LMS and Delite objects
 *
 * Can be used when printing traces making them easier to read
 */

import scala.virtualization.lms.internal.{ Effects, Expressions, FatExpressions }

trait PPrinter {
  val IR: Expressions with Effects with FatExpressions
  import IR._

  /**
   * Base trait used to print elements of type T
   */
  trait PPrint[-T] {
    def toString(elem: T): String
  }

  def pprint[T](elem: T)(implicit printer: PPrint[T] = defaultPrinter): String = {
    printer.toString(elem)
  }

  val defaultPrinter = new PPrint[Any] {
    def toString(elem: Any) = elem.toString
  }

  implicit def stmPrinter: PPrint[Stm] = new PPrint[Stm] {

    def toString(stm: Stm) = stm match {
      // TODO: why doens't this pickup the manifest printer on it's own
      case TP(lhs, rhs) => s"${pprint(lhs)}: ${pprint(lhs.tp)(manifestPrinter)} = ${pprint(rhs)}"
      case TTP(lhs, mhs, rhs) => s"FatTP : $stm"
    }
  }

  implicit def defPrinter[T]: PPrint[Def[T]] = new PPrint[Def[T]] {

    def toString(elem: Def[T]) = elem match {
      case Reflect(deff, summary, deps) => s"Reflect(${pprint(deff)}, ${pprint(summary)}, ${pprint(deps)})"
      case Reify(exp, summary, effects) => s"Reify(${pprint(exp)}, ${pprint(summary)}, ${pprint(effects)})"
      case d => d.toString
    }
  }

  implicit def listPrinter[T] = new PPrint[List[T]] {
    def toString(l: List[T]) = {
      l.map(pprint).toString
    }
  }

  implicit def summaryPrinter = new PPrint[Summary] {

    lazy val P = Pure()
    lazy val S = Simple()
    lazy val G = Global()
    lazy val A = Alloc()
    lazy val C = Control()

    def toString(summary: Summary) = {
      summary match {
        case P => "Pure"
        case S => "Simple"
        case G => "Global"
        case A => "Alloc"
        case C => "Control"
        case _ => {
          val boolElems = Map(
            "maySimple" -> summary.maySimple,
            "mstSimple" -> summary.mstSimple,
            "mayGlobal" -> summary.mayGlobal,
            "mstGlobal" -> summary.mstGlobal,
            "resAlloc" -> summary.resAlloc,
            "control" -> summary.control)

          val listElems = Map(
            "mayRead" -> summary.mayRead,
            "mstRead" -> summary.mstRead,
            "mayWrite" -> summary.mayWrite,
            "mstWrite" -> summary.mstWrite)

          val stringElems = boolElems.collect { case (name, true) => name } ++
            listElems.collect { case (name, syms) if syms.nonEmpty => s"$name = $syms" }

          stringElems.mkString("Summary(", ", ", ")")
        }
      }
    }
  }

  implicit def manifestPrinter[T] = new PPrint[Manifest[T]] {

    def shorten(typ: String): String = {
      if (!typ.contains(']')) {
        val lastDot = typ.lastIndexOf('.')
        typ.substring(lastDot + 1)
      } else {
        val (base, param) = typ.span(_ != '[')
        s"${shorten(base)}[${shorten(param.tail.init)}]"
      }
    }

    def toString(manifest: Manifest[T]) = shorten(manifest.toString)
  }
}
package scala.virtualization.lms
package util

import java.io.PrintStream
import internal._

/**
 * Use to record a full compilation trace with transformers and state of the IR in between
 * The output is then outputted as json or in a readable text format
 *
 * Example usage:
 *    val test: Rep[Int] => Rep[Unit] = ???
 *    val tree = reifyEffects(test(fresh[Int]))
 *    val export = new util.ExportTransforms {val IR: p.type = p}
 *    export.addTransform("Vertical Fusion", new common.LoopFusionVerticalTransformer {val IR: p.type = p})
 *    export.addTransform("Horizontal Fusion", new common.LoopFusionHorizontalTransformer {val IR: p.type = p})
 *    val output = new java.io.PrintStream("trace.json")
 *    export.withStream(output).run(tree)
 *
 *    // or export.withStream(output).run(tree, format = export.TextLog) for text representation
 */
trait ExportTransforms extends PPrinter {

  val IR: Expressions with Effects with FatExpressions
  import IR._

  private trait JsonAble {
    def toJson: String
  }
  private def toJsonArray(elements: TraversableOnce[JsonAble]): String = {
    elements.map(_.toJson).mkString("[", ",", "]")
  }

  /**
   * Simpler version of scala-virtualized's SourceContext
   * @param file    The name of the source
   * @param line    The line number
   * @param offset  The character offset on the line
   */
  private case class SourceLocation(file: String, line: Int, offset: Int, parent: Option[SourceLocation]) extends JsonAble {
    def toJson: String = s"""
    {
      "file"    : "$file",
      "line"    : $line,
      "offset"  : $offset,
      "parent"  : ${parent.map(_.toJson).getOrElse("null")}
    }
    """
  }

  /**
   * Semi-structured metadata that is being recorded for each statement in the IR
   * @param id        The id of the symbol that the statement defines
   * @param repr      A string representation of the statement
   * @param comments  Additional metadata
   */
  private case class StmInfo(id: Int, repr: String, pos: Seq[SourceLocation], comments: Seq[String], parent: Option[StmInfo], childrens: Seq[StmInfo] = Seq()) extends JsonAble {
    def addChild(stm: StmInfo) = this.copy(childrens = childrens :+ stm)
    def toJson: String = s"""
      {
        "id"        : $id,
        "repr"      : "$repr",
        "pos"       : ${toJsonArray(pos)},
        "comments"  : ${comments.map(comment => s""""$comment"""").mkString("[", ",", "]")},
        "parentId"  : ${parent.map(_.id).getOrElse("null")},
        "childrens" : ${toJsonArray(childrens)}
      }"""

  }

  /**
   * Represents a transformation pass
   * @param name    The name of the transformer
   * @param before  State of the IR before transformation
   * @param after   State of the IR after transformation
   */
  private case class TransformInfo(name: String, before: Seq[StmInfo], after: Seq[StmInfo]) extends JsonAble {
    def toJson: String = s"""
    {
      "name"    : "$name",
      "before"  : ${toJsonArray(before)},
      "after"   : ${toJsonArray(after)}
    }
    """
  }

  type Transformer = internal.AbstractTransformer { val IR: ExportTransforms.this.IR.type }

  private var tranformers: Seq[(String, Transformer)] = Seq.empty
  private var out: PrintStream = System.out
  private var log: Seq[TransformInfo] = Seq.empty

  /** Add a transformer to the list that need to be tracked */
  def addTransform(name: String, transform: Transformer): Unit = {
    tranformers :+= (name, transform)
  }

  def addTransform(transform: common.FixpointTransformer { val IR: ExportTransforms.this.IR.type }): Unit = {
    addTransform(transform.getInfoString, transform)
  }

  /** Sets the output stream for the export */
  def withStream(stream: PrintStream): this.type = {
    out = stream
    this
  }

  sealed trait Format
  object Json extends Format
  object TextLog extends Format

  /**
   * Run all of the transforms on the current block,
   * exporting all of the intermediate results along the way
   */
  def run[A: Manifest](block: Block[A], format: Format = Json): Unit = {
    log = Seq.empty
    val printer = new IRPrinter { val IR: ExportTransforms.this.IR.type = ExportTransforms.this.IR }

    var b: Block[A] = block
    for ((name, t) <- tranformers) {
      val before = printer.run(b)
      val res = t.apply(b)
      val after = printer.run(res)
      log :+= TransformInfo(name, before, after)
      b = res
    }

    format match {
      case Json => out.println(log.map(_.toJson).mkString("[", ",", "]"))
      case TextLog => {
        def printLevel(stm: StmInfo, level: Int = 0): Unit = {
          out.println(".." * level + stm.repr)
          stm.childrens.foreach(printLevel(_, level + 1))
        }
        def printTitle(title: String) = {
          out.println(title)
          out.println("=" * title.length)
        }

        for (t <- log) {
          printTitle(t.name)
          printTitle("Before")
          t.before.foreach(printLevel(_))
          printTitle("After")
          t.after.foreach(printLevel(_))
          out.println()
        }
      }
    }
  }

  /** Helper class used to output a representation of the IR between each transform */
  private trait IRPrinter extends FatBlockTraversal {
    val IR: ExportTransforms.this.IR.type
    import IR._

    private var currentBlock = new scala.util.DynamicVariable(Option.empty[Block[Any]])
    private var currentStm = Option.empty[StmInfo]
    private var topLevelStms = Seq.empty[StmInfo]

    override def traverseStm(stm: Stm) = stm match {
      case TP(lhs, rhs) =>

        var comments = Seq(
          s"syms: ${syms(rhs)}",
          s"symsFreq: ${symsFreq(rhs)}",
          s"boundSyms: ${boundSyms(rhs)}",
          s"effectSyms: ${effectSyms(rhs)}",
          s"readSyms: ${readSyms(rhs)}",
          s"blocks: ${blocks(rhs)}",
          s"enclosing block: ${currentBlock.value}")

        var parentStm = currentStm
        def toSourceLocation(srcCtx: scala.reflect.SourceContext): SourceLocation = {
          val parent = srcCtx.parent.map(toSourceLocation)
          SourceLocation(srcCtx.fileName, srcCtx.line, srcCtx.charOffset, parent)
        }
        val position = stm.lhs.flatMap(_.pos).map(toSourceLocation)
        currentStm = Some(StmInfo(lhs.id, pprint(stm), position, comments, parentStm))

        blocks(rhs).zipWithIndex foreach {
          case (blk, idx) =>
            currentBlock.withValue(Some(blk)) {
              traverseBlock(blk)
            }
        }

        parentStm match {
          case Some(s) =>
            currentStm = Some(s.addChild(currentStm.get))
          case None =>
            topLevelStms :+= currentStm.get
            currentStm = None
        }
    }

    /**
     * Traverses the whole IR and returns a semi-structured represantation
     */
    def run[A: Manifest](block: Block[A]): Seq[StmInfo] = {
      topLevelStms = Seq.empty
      traverseBlock(block)
      topLevelStms
    }

  }

}
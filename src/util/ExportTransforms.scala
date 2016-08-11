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

  /**
   * Simple type class expressing the fact that a type can be serialized to json
   */
  private trait JsonAble[T] {
    def toJson(elem: T): String
  }

  private def json[T: JsonAble](value: T): String = implicitly[JsonAble[T]].toJson(value)

  private implicit def jsonAbleSeq[T: JsonAble]: JsonAble[Seq[T]] = new JsonAble[Seq[T]] {
    val elemSerializer = implicitly[JsonAble[T]]
    def toJson(elem: Seq[T]): String = {
      elem.map(elemSerializer.toJson).mkString("[", ",", "]")
    }
  }

  private implicit def jsonAbleMap[K: JsonAble, V: JsonAble]: JsonAble[Map[K, V]] = new JsonAble[Map[K, V]] {
    val keySerializer = implicitly[JsonAble[K]]
    val valueSerializer = implicitly[JsonAble[V]]
    def toJson(elem: Map[K, V]): String = {
      elem.map {
        case (key, value) => s"${keySerializer.toJson(key)}:${valueSerializer.toJson(value)}"
      }.mkString("{", ",", "}")
    }
  }

  private implicit def jsonAbleOpt[T: JsonAble]: JsonAble[Option[T]] = new JsonAble[Option[T]] {
    val elemSerializer = implicitly[JsonAble[T]]
    def toJson(elem: Option[T]): String = {
      elem.fold("null")(elemSerializer.toJson)
    }
  }

  private implicit object String2Json extends JsonAble[String] {
    def toJson(elem: String): String = s""""$elem""""
  }

  private implicit object Int2Json extends JsonAble[Int] {
    def toJson(elem: Int): String = elem.toString
  }

  private def jsonObject(elems: (String, String)*) = elems.map { case (key, value) => s"${json(key)}:$value" }.mkString("{", ",", "}")

  /**
   * Simpler version of scala-virtualized's SourceContext
   * @param file    The name of the source
   * @param line    The line number
   * @param offset  The character offset on the line
   */
  private case class SourceLocation(file: String, line: Int, offset: Int)
  private implicit object SourceLocation2Json extends JsonAble[SourceLocation] {
    def toJson(elem: SourceLocation) = jsonObject(
      "file" -> json(elem.file),
      "line" -> json(elem.line),
      "offset" -> json(elem.offset))
  }

  /**
   * Metadata that is being recorded for each statement in the IR
   * @param id        The id of the symbol that the statement defines
   * @param repr      A string representation of the statement
   * @param pos       A list of the SourceContext history for this statement
   * @param comments  Additional metadata
   */
  private case class StmInfo(id: Int, repr: String, pos: Seq[Seq[SourceLocation]], comments: Map[String, String])
  private implicit object StmInfo2Json extends JsonAble[StmInfo] {
    def toJson(elem: StmInfo) = jsonObject(
      "id" -> json(elem.id),
      "repr" -> json(elem.repr),
      "pos" -> json(elem.pos),
      "comments" -> json(elem.comments))
  }

  /**
   * Represents a scoped statement, as it was scheduled by lms
   * @param stmId    The symbol id that this statement defines
   * @param parent   The optional parent for this node if it is scheduled in an inneer scope
   * @param children All the nodes in the direct inner scopes of this node
   */
  private case class IRNode(stmId: Int, parent: Option[IRNode], children: Seq[IRNode] = Seq.empty) {
    def addChild(child: IRNode) = this.copy(children = this.children :+ child)
  }
  private implicit object IRNode2Json extends JsonAble[IRNode] {
    def toJson(elem: IRNode) = jsonObject(
      "stmId" -> json(elem.stmId),
      "parent" -> json(elem.parent),
      "children" -> json(elem.children))
  }

  /**
   * Represents a transformation pass
   * @param name    The name of the transformer
   * @param before  Schedule before transformation
   * @param after   Schedule after transformation
   */
  private case class TransformInfo(name: String, before: Seq[IRNode], after: Seq[IRNode])
  private implicit object TransformInfo2Json extends JsonAble[TransformInfo] {
    def toJson(elem: TransformInfo) = jsonObject(
      "name" -> json(elem.name),
      "before" -> json(elem.before),
      "after" -> json(elem.after))
  }

  /**
   * Represents the full trace being recorded
   * @param transforms  The list of transformation passes that have occured
   * @param fullGraph   The full graph with all the nodes that have been created by lms
   */
  private case class Trace(transforms: Seq[TransformInfo], fullGraph: Seq[StmInfo])
  private implicit object Trace2Json extends JsonAble[Trace] {
    def toJson(elem: Trace) = jsonObject(
      "transforms" -> json(elem.transforms),
      "fullGraph" -> json(elem.fullGraph))
  }

  private def toSourceLocation(srcCtx: scala.reflect.SourceContext): Seq[SourceLocation] = {
    SourceLocation(srcCtx.fileName, srcCtx.line, srcCtx.charOffset) +: srcCtx.parent.toSeq.flatMap(toSourceLocation)
  }

  private def toStmInfo(stm: Stm): StmInfo = {

    val TP(sym @ Sym(id), rhs) = stm

    var comments = Map(
      "syms" -> syms(rhs).toString,
      "symsFreq" -> symsFreq(rhs).toString,
      "boundSyms" -> boundSyms(rhs).toString,
      "effectSyms" -> effectSyms(rhs).toString,
      "readSyms" -> readSyms(rhs).toString,
      "blocks" -> blocks(rhs).toString)
    //s"enclosing block: ${currentBlock.value}")*/

    StmInfo(id, pprint(stm), sym.pos.map(toSourceLocation), comments)
  }

  type Transformer = internal.AbstractTransformer { val IR: ExportTransforms.this.IR.type }

  private var tranformers: Seq[(String, Transformer)] = Seq.empty
  private var out: PrintStream = System.out

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
    var transforms: Seq[TransformInfo] = Seq.empty
    val printer = new IRPrinter { val IR: ExportTransforms.this.IR.type = ExportTransforms.this.IR }

    var b: Block[A] = block
    for ((name, t) <- tranformers) {
      val before = printer.run(b)
      val res = t.apply(b)
      val after = printer.run(res)
      transforms :+= TransformInfo(name, before, after)
      b = res
    }
    val fullGraph = globalDefs.map(toStmInfo)

    format match {
      case Json => out.println(json(Trace(transforms, fullGraph)))
      case TextLog => {
        val stmMap = fullGraph.map(stm => stm.id -> stm).toMap

        def printLevel(node: IRNode, level: Int = 0): Unit = {
          out.println(".." * level + stmMap(node.stmId))
          node.children.foreach(printLevel(_, level + 1))
        }
        def printTitle(title: String) = {
          out.println(title)
          out.println("=" * title.length)
        }

        for (t <- transforms) {
          printTitle(t.name)
          printTitle("Before")
          t.before.foreach(printLevel(_))
          printTitle("After")
          t.after.foreach(printLevel(_))
          out.println()
        }

        printTitle("Full Graph")
        for (stm <- fullGraph) {
          out.println(stm.repr)
        }
      }
    }
  }

  /** Helper class used to output a representation of the IR between each transform */
  private trait IRPrinter extends FatBlockTraversal {
    val IR: ExportTransforms.this.IR.type
    import IR._

    private var currentBlock = new scala.util.DynamicVariable(Option.empty[Block[Any]])
    private var currentStm = Option.empty[IRNode]
    private var topLevelStms = Seq.empty[IRNode]

    override def traverseStm(stm: Stm) = stm match {
      case TP(lhs, rhs) =>
        var parentStm = currentStm

        currentStm = Some(IRNode(lhs.id, parentStm))

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
    def run[A: Manifest](block: Block[A]): Seq[IRNode] = {
      topLevelStms = Seq.empty
      traverseBlock(block)
      topLevelStms
    }

  }

}
package scala.virtualization.lms.internal
import scala.reflect.SourceContext

trait IRVisitor extends FatBlockTraversal { self =>
  import IR._

  val name: String = self.getClass.getName
 
  def preprocess[A:Manifest](b: Block[A]): Block[A] = { b }
  def postprocess[A:Manifest](b: Block[A]): Block[A] = { b }

  /**
   * A single iteration of the traversal
   */ 
  def runOnce[A:Manifest](s: Block[A]): Block[A] = { traverseBlock(s); (s) }

  def run[A:Manifest](b: Block[A]): Block[A] = { 
    printlog("Beginning " + name)
    val curBlock = preprocess(b)
    val resultBlock = runOnce(curBlock)
    val outputBlock = postprocess(resultBlock) 
    
    if (hadErrors) { printlog(name + " completed with errors") }
    else           { printlog("Completed " + name) }
    (outputBlock)
  }

  override def traverseStm(stm: Stm): Unit = super.traverseStm(stm)
}

abstract class IRPrinter extends IRVisitor {
  import IR._
  override val name = "Printer"
  override def traverseStm(stm: Stm): Unit = {
    super.traverseStm(stm)
    stm match { 
      case TP(s,d) => 
        printmsg(strDef(s))
        printmsg("\tsyms: " + syms(d))
      case _ => //
    }
  }
  override def run[A:Manifest](b: Block[A]) = {
    printmsg("Program IR\n---------------")
    runOnce(b)
  }
}

trait IterativeIRVisitor extends IRVisitor {
  import IR._

  var MAX_ITERS: Int = 10   // maximum number of iterations to run
  var MAX_RETRIES: Int = 1  // maximum number of retries to allow
  var runs = 0              // Current analysis iteration
  var retries = 0           // Current retry
  val debugMode = false 

  var changed: Boolean = true    // Flag for if any metadata has changed
  def notifyChange() { changed = true }
 
  def hasConverged: Boolean = !changed
  def hasCompleted: Boolean = true

  def failedToConverge() { warn(name + " did not converge within " + MAX_ITERS + " iterations.") }
  def failedToComplete() { warn(name + " reached convergence but did not report completion.") }

  lazy val printer = new IRPrinter{val IR: IterativeIRVisitor.this.IR.type = IterativeIRVisitor.this.IR }

  private var _retry = false
  /**
   * Function to be called to try to recover when visitor converged but did not complete
   * In postprocess, modify state, then call resume() to resume looping. Resets run number.
   * Can also implement auto-increase of MAX_ITERS using resume() in postprocess
   */
  def resume() { _retry = true }

  /**
   * Run traversal/analysis on a given block until convergence or maximum iterations
   */
  override def run[A:Manifest](b: Block[A]): Block[A] = {
    printlog("Beginning " + name)
    var curBlock = preprocess(b)
    do {
      runs = 0
      _retry = false
      while (!hasConverged && runs < MAX_ITERS) { // convergence condition
        runs += 1
        changed = false
        curBlock = runOnce(curBlock)
      } 
      curBlock = postprocess(curBlock)
      if (_retry && retries < MAX_RETRIES) { retries += 1; printlog(name + " became stuck - retrying (retry " + retries + ")") }
    } while (_retry)

    if (!hasCompleted && runs > MAX_ITERS) { failedToConverge() }
    else if (!hasCompleted)                { failedToComplete() }
    else if (hadErrors)                    { printlog(name + " completed with errors") }
    else if (debugMode)                    { printlog("Completed " + name) }
    (curBlock)
  }    

  override def traverseStm(stm: Stm): Unit = super.traverseStm(stm)
}

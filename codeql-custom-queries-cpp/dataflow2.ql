/**
 * @kind problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

class MyConfiguration extends TaintTracking::Configuration {
  MyConfiguration() { this = "MyConfiguration" }
  
  override predicate isSource(DataFlow::Node source) {
    exists(MemberVariable var | var.getName() = "FSM__DOT__data" and source.asExpr() = var.getAnAccess())
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(MemberVariable var | var.getName() = "out" and sink.asExpr() = var.getAnAssignment())
  }

  override predicate isSanitizer(DataFlow::Node node) {
    exists(GuardCondition gc, MemberVariable guard | 
      guard.hasName("secure") and
      gc.getAChild*() = guard.getAnAccess() and 
      gc.controls(node.asExpr().getBasicBlock(), _)
    )
  }
}

from MyConfiguration config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink.getNode(), source, sink
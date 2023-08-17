/**
 * @kind problem
 */

 import cpp
 import semmle.code.cpp.dataflow.DataFlow
 import semmle.code.cpp.dataflow.TaintTracking

class AssetSecurityConfiguration extends TaintTracking::Configuration {
  AssetSecurityConfiguration() {this = "AssetSecurityConfiguration"}

  override predicate isSource(DataFlow::Node node) {
    exists(MemberVariable asset | asset.getName() = "openMSP430__DOT__pc" | node.asExpr() = asset.getAnAccess())
  }

  override predicate isSink(DataFlow::Node node) {
    exists(MemberVariable unsecure_loc | 
      unsecure_loc.getName() = "dbg_uart_txd" | 
      node.asExpr() = unsecure_loc.getAnAssignment()
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    exists(GuardCondition gc, MemberVariable guard | 
      guard.hasName("dbg_en_s") and
      gc.getAChild*() = guard.getAnAccess() and 
      gc.controls(node.asExpr().getBasicBlock(), _)
    )
    // or
    // exists(BitwiseAndExpr andExpr, MemberVariable guard |
    //   guard.hasName("dbg_en_s") and 
    //   andExpr.getAChild*() = guard.getAnAccess() and
    //   andExpr.getAChild*() = node.asExpr()
    // )
  }
}

from
  AssetSecurityConfiguration conf, 
  DataFlow::PathNode source, 
  DataFlow::PathNode sink
where
  conf.hasFlowPath(source, sink)
select
  source, source, sink, "error"

/* debug */
// from MemberVariable mv
// where mv.hasName("dbg_en_s")
// select mv.getAnAccess()

// from
//   GuardCondition gc, MemberVariable guard, MemberVariable asset, DataFlow::Node node, Expr access
// where
//   guard.hasName("secure") and
//   asset.hasName("secure_state") and
//   gc.getAChild*() = guard.getAnAccess() and
//   gc.controls(node.asExpr().getBasicBlock(), _)
// select
//   gc, node.asExpr()
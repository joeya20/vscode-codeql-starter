/**
 * @kind problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.valuenumbering.GlobalValueNumbering
// import DataFlow::PathGraph


// class MyConfiguration extends DataFlow::Configuration {
//   MyConfiguration() { this = "MyConfiguration" }
  
//   override predicate isSource(DataFlow::Node source) {
//     exists(MemberVariable var | var.getName() = "secure_state" and source.asExpr() = var.getAnAccess())
//   }

//   override predicate isSink(DataFlow::Node sink) {
//     exists(MemberVariable var | var.getName() = "buggy_FSM__DOT__ns" and sink.asExpr() = var.getAnAssignment())
//   }
// }

// from MyConfiguration config, DataFlow::PathNode source, DataFlow::PathNode sink
// where config.hasFlowPath(source, sink)
// select sink.getNode(), source, sink

// from DataFlow::Node source, DataFlow::Node sink, MemberVariable asset, MemberVariable unsecure_loc
// where TaintTracking::localTaint(source, sink)
// and asset.getName() = "secure_state"
// and unsecure_loc.getName() = "buggy_FSM__DOT__ns"
// and source.asExpr() = asset.getAnAccess()
// and sink.asExpr() = unsecure_loc.getAnAssignedValue()
// select source, sink

// from MemberVariable var
// where var.getName() = "buggy_FSM__DOT__ns"
// select var.getAnAssignment()

// class AssetSecurityConfiguration extends TaintTracking::Configuration {
//   AssetSecurityConfiguration() {this = "AssetSecurityConfiguration"}

//   override predicate isSource(DataFlow::Node node) {
//     exists(MemberVariable asset | asset.getName() = "openMSP430__DOT__pc" | node.asExpr() = asset.getAnAccess())
//   }

//   override predicate isSink(DataFlow::Node node) {
//     exists(MemberVariable unsecure_loc | 
//       unsecure_loc.getName() = "dbg_uart_txd" | 
//       node.asExpr() = unsecure_loc.getAnAssignment()
//     )
//   }

//   override predicate isSanitizer(DataFlow::Node node) {
//     exists(GuardCondition gc, MemberVariable guard | 
//       guard.hasName("dbg_en_s") and
//       gc.getAChild*() = guard.getAnAccess() and 
//       gc.controls(node.asExpr().getBasicBlock(), _)
//     )
//     // or
//     // exists(BitwiseAndExpr andExpr, MemberVariable guard |
//     //   guard.hasName("dbg_en_s") and 
//     //   andExpr.getAChild*() = guard.getAnAccess() and
//     //   andExpr.getAChild*() = node.asExpr()
//     // )
//   }
// }

// from
//   AssetSecurityConfiguration conf, 
//   DataFlow::PathNode source, 
//   DataFlow::PathNode sink
// where
//   conf.hasFlowPath(source, sink)
// select
//   source, source, sink, "error"

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

class RTG011Conf extends TaintTracking::Configuration {

  RTG011Conf() {this = "RTG011Conf"}

  override predicate isSource(DataFlow::Node node) {
    exists(MemberVariable asset | asset.getName() = "debug_update" | node.asExpr() = asset.getAnAccess())
  }

  override predicate isSink(DataFlow::Node node) {
    exists(MemberVariable unsecure_loc | 
      unsecure_loc.getName() = "trng__DOT__mixer_inst__DOT__mixer_ctrl_reg" | 
      node.asExpr() = unsecure_loc.getAnAssignment()
    )
  }
}

// from
//   RTG011Conf conf, 
//   DataFlow::Node source, 
//   DataFlow::Node sink
// where
//   conf.hasFlow(source, sink)
// select
//   source.asExpr(), "insecure flow to @", sink

class AccCtrlConfiguration extends TaintTracking::Configuration {
  AccCtrlConfiguration() {this = "AccCtrlConfiguration"}

  override predicate isSource(DataFlow::Node node) {
    exists(MemberVariable asset | asset.getName() = "wd" | node.asExpr() = asset.getAnAccess())
  }

  override predicate isSink(DataFlow::Node node) {
    exists(MemberVariable unsecure_loc | 
      unsecure_loc.getName() = "ctrl__DOT__secure_reg_u0__DOT__data" | 
      node.asExpr() = unsecure_loc.getAnAssignment()
    )
  }

  override predicate isSanitizer(DataFlow::Node node) {
    exists(GuardCondition gc, MemberVariable guard, Expr val | 
      val.getValue().toInt() = 1 and
      guard.hasName("ctrl__DOT__cfg_reg") and
      gc.getAChild*() = guard.getAnAccess() and 
      gc.controls(node.asExpr().getBasicBlock(), _) and
      gc.comparesEq(guard.getAnAccess(), val, 0, true, true)
    )
  }
}

// from
//   AccCtrlConfiguration conf, 
//   DataFlow::Node source, 
//   DataFlow::Node sink
// where
//   conf.hasFlow(source, sink)
// select
//   source.asExpr(), "insecure flow to @", sink

// from GuardCondition gc, MemberVariable guard, Expr val, GVN v
// where
//   val.getValue().toInt() = 1 and
//   guard.hasName("ctrl__DOT__cfg_reg") and
//   gc.getAChild*() = guard.getAnAccess() and
//   gc.getAChild*() = val and
//   // v = globalValueNumber(val)
//   v = globalValueNumber(guard.getAnAccess())
// select
//   gc, v.getAnExpr()


from Class c
where c.hasName("Vchip_sim_tb")
select c.getADeclaration()
import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.valuenumbering.GlobalValueNumbering
 // import DataFlow::PathGraph
 
class MyConfiguration extends TaintTracking::Configuration {
MyConfiguration() { this = "MyConfiguration" }

override predicate isSource(DataFlow::Node source) {
    exists(MemberVariable var | var.getName() = "sec_reg__DOT__data" and source.asExpr() = var.getAnAccess())
}

override predicate isSink(DataFlow::Node sink) {
    exists(MemberVariable var | var.getName() = "out_o" and sink.asExpr() = var.getAnAssignment())
}

override predicate isSanitizer(DataFlow::Node node) {
    exists(GuardCondition gc, MemberVariable guard, Expr i | 
        // get rhs of conditional
        i.getValue().toInt() = 2 and
        //get guard variable that dictates flow
        guard.hasName("sec_reg__DOT__cfg") and        
        // check guard condition
        gc.getAChild*() = guard.getAnAccess() and         
        gc.ensuresEq(i, guard.getAnAccess(), 0, node.asExpr().getBasicBlock(), true)
    )
  }
}

from
    MyConfiguration conf,
    DataFlow::Node source, 
    DataFlow::Node sink
where
    conf.hasFlow(source, sink)
select
    source.asExpr(), "insecure flow to @", sink.asExpr()
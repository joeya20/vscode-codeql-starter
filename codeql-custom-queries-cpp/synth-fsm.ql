import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

class MyConfiguration extends TaintTracking::Configuration {
MyConfiguration() { this = "MyConfiguration" }

override predicate isSource(DataFlow::Node source) {
    exists(MemberVariable var | var.getName() = "fsm__DOT__data" and source.asExpr() = var.getAnAccess())
}

override predicate isSink(DataFlow::Node sink) {
    exists(MemberVariable var | var.getName() = "out" and sink.asExpr() = var.getAnAssignment())
}

override predicate isSanitizer(DataFlow::Node node) {
    exists(GuardCondition gc, MemberVariable guard, EnumConstant e, Expr i | 
        // get enum DONE
        e.hasName("DONE") and
        // get rhs of conditional
        i.getValue().toInt() = e.getValue().toInt() and
        //get guard variable that dictates flow
        guard.hasName("fsm__DOT__state") and        
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
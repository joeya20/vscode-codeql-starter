/**
 * @kind problem
 */

import cpp
import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.dataflow.TaintTracking

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
  
  from
    RTG011Conf conf, 
    DataFlow::Node source, 
    DataFlow::Node sink
  where
    conf.hasFlow(source, sink)
  select
    source.asExpr(), "insecure flow source"
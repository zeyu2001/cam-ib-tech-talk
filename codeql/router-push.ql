/**
 * Potentially unsafe use of router.push leads to XSS in Next.js
 *
 * @name Unsafe router.push
 * @kind problem
 * @problem.severity warning
 * @id javascript/router-push
 */

import javascript

class UnsafeRouterPushConfiguration extends TaintTracking::Configuration {
  UnsafeRouterPushConfiguration() { this = "UnsafeRouterPushConfiguration" }

  override predicate isSource(DataFlow::Node source) {
    source instanceof RemoteFlowSource or
    source instanceof ClientRequest::Range
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(DataFlow::MethodCallNode call, DataFlow::Node receiver |
      call.getMethodName() = "push" and
      call.getReceiver() = receiver and
      receiver.getALocalSource().(DataFlow::InvokeNode).getCalleeName() = "useRouter" and
      sink = call.getArgument(0)
    )
  }

  override predicate isAdditionalTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(DataFlow::ArrayCreationNode array |
      pred = array.getAnElement() and
      succ = array
    )
    or
    exists(DataFlow::MethodCallNode call |
      call.getMethodName().regexpMatch("find|filter|some|every|map") and
      pred = call.getReceiver() and
      succ = call.getABoundCallbackParameter(1, 0)
    )
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink, UnsafeRouterPushConfiguration config
where config.hasFlowPath(source, sink)
select sink.getNode(), "Potentially unsafe router.push with $@.", source.getNode(),
  "untrusted input"

# PCR in TLA+

PCR is a parallel programming pattern, which describes computations
performed concurrently by communicating Producers,
Consumers, and Reducers, each one being either a basic
function (business logic), or a nested PCR. It combines in
a single and composable pattern several concepts like collectives, 
eureka computations, unbounded iteration and recursion, 
and stream programming. It was firstly introduced in [[1]](https://link.springer.com/article/10.1007/s10009-017-0465-2).

The current project, resulting from a master thesis, seek to provide
a formal framework based on the TLA+ specification language to 
- Express high level PCR designs and prove their functional 
correctness in the sense that their parallel computation computes a 
given mathematical function.
- Be able to formally relate different PCR designs by way of refinement. In particular,
to prove that a PCR with more parallelism is an implementation of a PCR with less parallelism.
- Leverage TLA+ related tools for mechanical verification, i.e. model checking and theorem proving.

# Iteration 001: Reps-Horwitz-Sagiv IFDS

Paper:

- Thomas W. Reps, Susan Horwitz, Shmuel Sagiv, "Precise Interprocedural
  Dataflow Analysis via Graph Reachability", POPL 1995, pp. 49-61.
- DOI/metadata: <https://dblp.org/rec/conf/popl/RepsHS95>
- PDF inspected: <https://web.stanford.edu/class/archive/cs/cs295/cs295.1086/papers/p49-reps.pdf>

## Core Claim

The paper defines the class of interprocedural finite distributive subset
problems: dataflow facts form a finite set, transfer functions operate over
powersets of those facts, and transfer functions distribute over the confluence
operator.  For this class, precise interprocedural dataflow analysis can be
reduced to reachability over an exploded supergraph, restricted to realizable
call/return paths.

## Mapping to This Repository

Already covered:

- `PcSastLean.IFDS`: exploded-supergraph nodes, call/return actions, valid path
  certificates, and checked reachability.
- `PcSastLean.IFDSFixpoint`: closed reached-set certificates for no-finding
  claims.
- `PcSastLean.IFDSSummary`: compressed path and summary-edge certificates that
  expand back to ordinary IFDS paths.
- `PcSastLean.IFDSCPGEmbedding`: one-way embedding from accepted IFDS path
  certificates into CPG-style path certificates.

Gap before this iteration:

- The repository checked IFDS artifacts after an exploded graph had already been
  produced.
- It did not formalize the paper's bridge from finite distributive subset
  transfer functions to exploded-supergraph edges.
- It did not state or prove that sparse fact-to-fact flow relations distribute
  over the subset confluence operator.

## Lean Patch

Added `PcSastLean.IFDSDistributive`.

New artifacts:

- `IFDSFactFlow`: sparse fact-to-fact flow relation.
- `applyFactFlow`: applies a finite relation to a set of input facts.
- `applyFactFlow_sound`: every output fact comes from some input fact and
  relation edge.
- `applyFactFlow_complete`: every relation edge whose source fact is present
  contributes its target fact.
- `applyFactFlow_append_distributes`: relational transfer distributes over
  list-union membership.
- `IFDSFlowEdge`: program-point edge annotated with a sparse fact-flow relation.
- `explodeFlowEdge` and `explodeFlowGraph`: compile sparse flow relations into
  ordinary IFDS exploded-supergraph edges.
- `flowHopsPath_to_IFDSPath`: a valid relational flow path lowers to an ordinary
  IFDS path.
- `ifds_flow_path_cert_sound`: a relational flow-path certificate implies
  `IFDSReachable` over the exploded graph.

This is a better integration point than the earlier path checker alone: the
theory now has a formal place where "finite distributive subset problem" enters
the checker architecture.

## Remaining Gaps

- No tabulation/worklist algorithm correctness proof.
- No complexity theorem such as the paper's polynomial bounds.
- No explicit zero-value convention.
- No meet-over-all-valid-path optimality theorem; we only prove certificate
  soundness for emitted paths.
- No frontend proof that real statements produce the emitted sparse relations.
- No IDE/weighted extension.

## Next Theorem Candidate

Add a small tabulation-closure certificate that is closed under relational
`IFDSFlowEdge`s rather than already-exploded `IFDSEdge`s.  That would move
no-finding certificates one layer closer to the IFDS paper's transfer-function
view.

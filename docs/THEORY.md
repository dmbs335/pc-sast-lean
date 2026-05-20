# PC-SAST: Proof-Carrying SAST

This project sketches a Lean verification layer for SAST results.

The core idea is to keep the analyzer fast and practical while moving the trust
boundary to a small proof checker:

1. Extract source code into a typed security IR with AST, CFG, data-flow, and
   source-location information.
2. Run SAST analyses such as taint analysis, IFDS, Code Property Graph queries,
   abstract interpretation, or CEGAR-style checkers.
3. Emit certificates: paths, graph edges, source/sink classifications, abstract
   facts, fixpoint witnesses, and sanitizer obligations.
4. Check those certificates in Lean against a formal policy and semantics.

Lean does not need to rediscover every finding. It only needs to check that a
finding, suppression, or "safe" claim follows from trusted definitions.

## Literature Backbone

- Kildall-style data-flow analysis: monotone transfer functions over program
  points.
- Cousot and Cousot abstract interpretation: sound approximation of concrete
  semantics by abstract domains and fixpoints.
- Reps, Horwitz, and Sagiv IFDS: precise interprocedural finite distributive
  subset analysis via graph reachability.
- Engler et al. bug-finding: infer system-specific programmer beliefs and detect
  contradictions.
- Code Property Graphs: combine AST, CFG, and dependence graphs so vulnerability
  templates become graph traversals.
- FlowDroid-style taint analysis: context-, flow-, field-, object-sensitive
  source-to-sink reasoning for application security.
- BLAST/SLAM/SDV: property-driven abstraction refinement and proof/error-trace
  artifacts.
- Verasco/CompCert: precedent for verified static analysis and verified compiler
  infrastructure in a proof assistant.

## Trust Boundary

Trusted:

- Lean kernel.
- Formal IR well-formedness definitions.
- Policy definitions: source, sink, sanitizer, bad trace.
- Certificate checker.

Untrusted:

- SAST engine implementation.
- Query optimizer.
- Ranking/triage model.
- LLM-generated explanations.
- Build-system extraction heuristics unless separately certified.

## Scope Corrections

The phrase "verified slice" is intentionally narrow in this repository.

- `Expr` and `Instr` are toy languages.  They are useful for proving the shape of
  taint, abstraction, sanitizer, fix, baseline, and triage theorems, but they do
  not model alias-through-pointer-arithmetic, async scheduling, callbacks,
  exceptions, reflection, or generated-code semantics.
- Procedure, dynamic, framework, and callback behavior is usually represented as
  a summary soundness obligation.  That is a checked boundary condition, not a
  proof that the real language feature has been modeled.
- Source-level claims are conditional.  `SourceToIRSound` is the bridge from
  source violations to IR violations, and real-language extractors that produce
  that certificate are not implemented yet.
- `SMTCore` currently checks only a tiny contradictory Boolean pivot.  It does
  not yet provide proof checking for LRA, EUF, strings, arrays, regexes, or
  theory lemmas.
- Object sensitivity currently uses abstract `Nat` context keys and proves that
  joining over those keys projects soundly to allocation-site abstraction.  It is
  not yet a real call-string-k or receiver-type sensitivity model.
- Framework modeling is a toy may-route and guard-chain model.  Path templates,
  regex routing, content negotiation, middleware order, exception handlers, and
  transaction/query-builder APIs are outside the modeled semantics.
- CPG construction now has a small component-edge merge theorem from
  AST/CFG/PDG-style edges into typed CPG paths, but production
  AST/CFG/DDG/CDG extraction rules are still missing.
- Many `checked_X_sound` lemmas are intentionally checker-shape lemmas: Boolean
  certificate acceptance unfolds to the corresponding trusted proposition.  The
  more substantive theorems are the no-bug-hiding triage theorem, extraction
  transfer gates, IFDS/CPG certificate embeddings, heap/sanitizer abstraction
  soundness, and summary/compressed-path expansion.
- Precision is not generally proved here.  The current theory proves conditional
  soundness and no-bug-hiding, plus a few targeted precision theorems where
  checked structural evidence justifies suppressing a specific class of false
  positive.

## Claim Table

| Layer | Status | Lean artifact | Boundary |
| --- | --- | --- | --- |
| Toy expression taint | Verified | `expr_taint_sound`, graph finding certs | Only the tiny `Expr` language |
| Security IR | Verified inside model | `exec_sound`, branch/join, procedure summary theorems | `Instr` is minimal; real control/data effects are outside the IR |
| Mini source extraction | Verified | `miniExec_compile_exact`, `miniSourceToIRSound` | Only a tiny statement language with input, assign, sanitize, concat, and sink |
| Mini source branches | Verified | `mini_branch_sound`, `mini_branch_abstract_safety_implies_concrete_safety` | No real CFG, path feasibility, exceptions, callbacks, or async control flow |
| Mini source exceptions | Verified | `mini_try_catch_finally_sound`, `mini_try_catch_finally_abstract_safety_implies_concrete_safety` | No real stack unwinding, typed exceptions, promises, async rejection paths |
| Mini source callbacks | Verified | `mini_callback_sound`, `mini_callback_abstract_safety_implies_concrete_safety` | No event-loop ordering, async/await, promise chains, cancellation, or reentrancy |
| Rich source provenance | Conditional | `richSourceBackedRun_sound`, `richMultiSourceBackedRun_sound`, `collected_mini_rich_provs_cover_source_violations` | Correct source maps, parser spans, and generated-code origins remain external |
| Heap/alias abstraction | Conditional | heap may-points-to soundness, allocation-site/object-sensitive projection | No pointer arithmetic, native objects, reflection, or real call-string-k model |
| Offset pointer arithmetic | Conditional toy model | `offset_ptr_add_sound`, `readAbsPtr_sound`, `offset_writeMayPtr_sound`, `offset_load_sound` | No C/C++ pointer provenance, byte layout, UB, unsafe casts, or negative offsets |
| Sanitizers/templates/ORM | Verified inside model | context-indexed sanitizer capabilities, template slots, prepared-parameter rules | Parser-state completeness and framework APIs are not modeled |
| IFDS certificates | Verified/conditional | path, fixpoint, compressed summary cert soundness; sparse finite-distributive flow relations lower to exploded graph paths | Solver implementation is untrusted; real transfer-function extraction remains external |
| CPG certificates | Conditional | typed path certs, path-specific edge provenance, IFDS-to-CPG embedding, component-edge merge into CPG paths, traversal-template certificates | Real AST/CFG/DDG/CDG extraction provenance and production query-language compilation are incomplete |
| Suppression/no-bug-hiding | Conditional theorem | proof-carrying suppression and CI no-bug-hiding | Requires analyzer soundness and complete triage evidence |
| Source extraction | External obligation | `SourceToIRSound` transfer gates | No real-language extractor yet |
| SMT feasibility | Conditional toy checker | contradictory Boolean pivot, unsat-core witness, and implication-chain resolution | No LRA/EUF/string/array/theory proof checker yet |
| Framework/dynamic | Conditional toy model | route may-set, guard chain, literal/param route templates, dynamic summary obligations | No production framework semantics, regex routing, content negotiation, async/callback/exception semantics |
| Route-shadow suppression | Conditional precision theorem | `checked_route_shadow_not_concrete`, `shadowTriageComplete` | Full framework precedence, regex/converter constraints, middleware interactions remain external |
| Pointer-disjoint suppression | Conditional precision theorem | `checked_pointer_disjoint_not_concrete`, `pointerDisjointTriageComplete` | Real C/C++ provenance, byte layout, UB, unsafe casts, partial overlap, concurrency |
| General precision | Not modeled | Targeted conditional suppressions only | Broad FP reduction or recall/precision theorem |

The matching Lean-side ledger is `PcSastLean.AssumptionLedger`.  In particular,
`SourceLevelGateInputs` makes source-level CI claims require `SourceToIRSound`,
analyzer soundness, and complete proof-carrying triage.  The main modules also
carry module-level claim-boundary comments spelling out what is verified, what
is an external obligation, and what is not modeled.

## Verified Slice in This Repo

`PcSastLean.Basic` contains graph-level proof-carrying SAST:

- `expr_taint_sound`: if an abstract state over-approximates concrete taint,
  then taint detected in a concrete expression is also present abstractly.
- `accepted_finding_is_violation`: if the checker accepts a source-to-sink path
  certificate, then a policy violation is derivable in the trusted model.

`PcSastLean.SecurityIR` connects that certificate view to an executable security
IR:

- `Label.le`, `Store.le`: the abstract-interpretation precision order for taint.
- `Instr`: a minimal security IR with `source`, `assign`, `sanitize`, and `sink`.
- `step` and `exec`: executable taint semantics for the IR.
- `step_store_sound`: one-step transfer functions preserve store soundness.
- `exec_store_sound`: whole-program execution preserves store soundness.
- `exec_sound`: whole-program execution preserves both store soundness and the
  violation subset relation.  If concrete execution reports a sink violation,
  the abstract execution reports it too.
- `accepted_sink_cert_sound`: a sink certificate accepted by the checker refers
  to a real sink in the program.
- `accepted_concrete_finding_sound`: an accepted concrete finding certificate
  corresponds to a real violation in the IR execution.
- `accepted_concrete_safety_sound`: an accepted safety certificate means the IR
  execution has no sink violations.
- `accepted_abstract_safety_gate_sound`: if an abstract store over-approximates
  a concrete store and Lean accepts the abstract safety check, then the concrete
  program is safe.
- `branch_sound`: concrete branch execution chooses one side, while abstract
  branch execution analyzes both sides and joins the stores.  Lean proves the
  abstract branch over-approximates the concrete branch for both stores and sink
  violations.
- `branch_abstract_safety_implies_concrete_safety`: if the joined abstract branch
  has no violations, either concrete branch choice is safe.
- `SummarySound`: a procedure summary is trusted only when it over-approximates
  the callee body for every concrete/abstract input pair.
- `block_sound`: an instruction block is sound by the primitive transfer
  theorems; a call block is sound by its procedure summary.
- `blocks_sound`: interprocedural block sequences preserve store soundness and
  violation inclusion.
- `blocks_abstract_safety_implies_concrete_safety`: if summary-backed abstract
  block execution has no violations, concrete interprocedural execution is safe.
- `Proc`, `ProcSummary`, and `ProcSummarySound`: reusable procedure summaries
  now have the SAST-shaped interface `argument taints -> return taint +
  violations`.
- `proc_call_sound`: if the argument taints in the concrete caller are covered by
  the abstract caller and the procedure summary is sound, then the summarized
  abstract call covers the concrete call body, including return taint and sink
  violations.

`PcSastLean.HeapIR` adds heap/object-field and alias reasoning:

- `ConcreteHeapState`: variable taints, one concrete object per reference
  variable, and field taints.
- `AbsHeapState`: variable taints, may-points-to sets, and abstract field taints.
- `HeapSound`: variable taints are over-approximated, concrete objects appear in
  may-points-to sets, and concrete heap fields are covered by abstract fields.
- `readAbsField_sound`: reading a concrete object field is covered by joining all
  abstract may-points-to field labels.
- `heap_storeMayField_sound`: concrete field writes are covered by a
  may-points-to abstract write that joins the source taint only into target
  objects in the base variable's may-points-to set.
- `stepHeap_sound` and `execHeap_sound`: heap-aware execution preserves state
  soundness and violation inclusion.
- `heap_abstract_safety_implies_concrete_safety`: if the heap-aware abstract
  execution has no violations, the concrete heap execution has no violations.

`PcSastLean.BaselineGate` adds the most directly engineering-oriented theorem:

- `baseline_gate_linear`: if the linear abstract analysis result is covered by an
  approved baseline, then the concrete linear execution has no violation outside
  that baseline.
- `baseline_gate_blocks`: the same theorem for interprocedural block execution.
- `baseline_gate_heap`: the same theorem for heap-aware object-field execution.
- `sink_absence_from_baseline_*`: if a sink is not in the approved baseline, it
  cannot occur in concrete execution once the abstract result has been checked
  against the baseline.

This is stronger as a CI workflow than requiring a zero-finding program.  It
lets a project with legacy findings prove a precise release property:

> Every concrete vulnerability in this build is already in the approved
> baseline.

`PcSastLean.FixGate` adds an even more PR-oriented theorem:

- `fix_gate_linear`: if a patched linear abstract run no longer contains a
  particular sink, the patched concrete run cannot contain that sink.
- `fix_gate_blocks`: the same claim for interprocedural block execution.
- `fix_gate_heap`: the same claim for heap-aware object-field execution.
- `regression_fix_gate_heap`: if the old abstract run contained a sink and the
  patched abstract run removes it, Lean proves both the observed abstract
  regression and the patched concrete absence.

This is the security-fix workflow theorem:

> A patch is verified for vulnerability sink `S` when the sound abstract analysis
> of the patched program excludes `S`; then no concrete execution of the patched
> program can hit `S`.

`PcSastLean.DynamicObligations` handles dynamic language and framework features:

- `DynamicWitness`: a runtime/framework/generated-code/configuration witness that
  supplies a summary for a dynamic call.
- `DynamicBlockSound`: the witness summary must over-approximate the dynamic
  body.
- `dblocks_sound`: once every dynamic block has a sound witness, mixed
  static/dynamic execution preserves store soundness and violation inclusion.
- `dynamic_fix_gate`: a fix gate remains valid across dynamic calls only when
  their obligations are discharged.
- `dynamic_baseline_gate`: a baseline gate remains valid across dynamic calls
  only when their obligations are discharged.

This changes the theorem boundary:

> Dynamic behavior is not ignored.  It is an obligation.  If the obligation is
> not discharged, the fix/baseline theorem is unavailable.

Examples of acceptable witnesses include framework route extraction, generated
code extraction, runtime trace coverage, plugin allowlists, reflection target
sets, and configuration-derived call graphs.

`PcSastLean.SanitizerLattice` handles context-sensitive sanitizers:

- `SinkKind`: SQL, HTML, shell, and path sink contexts.
- `Protection`: a lattice-like protection record tracking which sink contexts a
  value is safe for.
- `SecLabel`: a security label carrying context-specific protections instead of
  a single clean/tainted bit.
- `sanitize_safe_for`: sanitizing for context `K` proves safety for `K`.
- `sanitize_preserves_existing`: adding one sanitizer does not erase previously
  proven protections.
- `wrong_context_sanitizer_does_not_prove_html_safe`: SQL sanitization does not
  prove HTML safety.
- `sexec_sound`: context-sensitive sanitizer execution preserves the soundness
  relation and violation inclusion.  The abstract run is not allowed to claim
  protections that the concrete run lacks.
- `sanitizer_fix_gate`: if a patched context-sensitive abstract run removes a
  sink, the patched concrete run cannot contain that sink.

This prevents an important SAST mistake:

> Sanitization is not global cleanliness.  It is a context-indexed capability.

`PcSastLean.SuppressionGate` handles false-positive reduction safely:

- `SoundSuppression`: a suppressed finding must carry an obligation proving that
  the corresponding concrete violation cannot occur.
- `ReportCoversUnsuppressed`: every abstract finding is either reported or
  suppressed.
- `suppression_gate`: if concrete violations are included in abstract findings,
  every abstract finding is reported or soundly suppressed, and every suppression
  is concrete-impossible, then every concrete violation is still reported.
- `heap_suppression_gate`: the same gate for heap-aware SAST.
- `sanitizer_suppression_gate`: the same gate for context-sensitive sanitizer
  analysis.

This turns path-feasibility, auth-guard, unreachable-route, and aliasing
false-positive suppressions into proof obligations:

> A finding may be hidden from the report only if Lean receives a witness that no
> concrete execution can realize that suppressed finding.

`PcSastLean.ExtractionGate` makes the source-to-IR boundary explicit:

- `SourceToIRSound`: every source-level violation must appear in the IR-level
  concrete violations.
- `extraction_fix_gate`: if extraction is sound and the IR fix gate removes a
  sink, then the source program also cannot hit that sink.
- `extraction_baseline_gate`: if extraction is sound and the IR concrete
  violations are covered by a baseline, source-level violations are covered too.
- `extraction_suppression_gate`: proof-carrying suppressions transfer back to
  source only when extraction is sound.
- `extraction_heap_fix_gate` and `extraction_sanitizer_fix_gate`: source-level
  fix gates for the heap-aware and context-sensitive sanitizer analyses.

This closes an important trust-boundary hole:

> Lean does not infer that real source code is safe merely because an IR is safe.
> It requires an extraction certificate connecting source behavior to IR
> behavior.  This repository does not yet contain a real-language extractor that
> produces such certificates.

`PcSastLean.MiniSourceExtraction` discharges the extraction assumption for a
small separate source language:

- `MiniStmtKind`: source-level statements for input, assignment, sanitizer,
  concatenation, and sink use.
- `miniStep` and `miniExec`: source-level semantics over the context-sensitive
  sanitizer store.
- `compileMiniStmt` and `compileMini`: extraction into `SInstr`.
- `miniStep_compile_exact`: one source step matches one compiled IR step.
- `miniExec_compile_exact`: whole-program source execution matches compiled IR
  execution.
- `miniSourceToIRSound`: the exactness theorem packaged as `SourceToIRSound`.

This is the first non-vacuous extractor slice:

> Source-level transfer gates are no longer demonstrated only by assuming
> extraction soundness.  For the mini source language, Lean proves the extraction
> certificate from separate source and IR semantics.

`PcSastLean.MiniSourceBranch` adds source-level branch/join reasoning for the
mini source language:

- `SecStore.join`: joins sanitizer stores by keeping only protections common to
  both branches.
- `miniExecConcreteBranch`: concrete source execution chooses one branch.
- `miniExecAbstractBranch`: abstract source execution analyzes both branches and
  joins stores/findings.
- `mini_branch_sound`: concrete branch execution is covered by abstract
  branch/join execution.
- `mini_branch_abstract_safety_implies_concrete_safety`: if the abstract
  branch/join result has no finding, either concrete branch choice is safe.

This narrows one earlier gap:

> Branch/join reasoning is now connected to the mini source layer, not only to a
> separate low-level IR theorem.  Real CFG construction, path feasibility,
> exceptions, callbacks, and async scheduling remain outside the model.

`PcSastLean.MiniSourceException` adds a toy source-level exception-flow slice:

- `miniExecConcreteTryCatch`: concrete execution follows either the protected
  path or the handler path.
- `miniExecAbstractTryCatch`: abstract execution analyzes both protected and
  handler paths using the mini source branch/join theorem.
- `miniExecConcreteTryCatchFinally` and `miniExecAbstractTryCatchFinally`: both
  forms execute a finalizer after the protected/handler choice.
- `mini_try_catch_finally_sound`: concrete try/catch/finally execution is covered
  by abstract handler/join execution.
- `mini_try_catch_finally_abstract_safety_implies_concrete_safety`: abstract
  safety implies concrete safety for either concrete exception outcome.

This is still deliberately small:

> Mini exception flow is no longer just a summary assumption, but production
> stack unwinding, typed exceptions, implicit throw edges, promises, async
> rejection paths, and framework error handlers remain external obligations.

`PcSastLean.MiniSourceCallback` adds a toy callback/event-flow slice:

- `MiniCallback`: a registered callback body with a registration id.
- `miniExecConcreteCallback`: concrete execution runs the main flow and may or
  may not invoke the callback.
- `miniExecAbstractCallback`: abstract execution runs the main flow and includes
  the possible callback invocation.
- `mini_callback_sound`: concrete optional callback execution is covered by the
  abstract callback-inclusive execution.
- `mini_callback_abstract_safety_implies_concrete_safety`: abstract callback
  safety implies concrete callback safety for either invocation outcome.

This handles one more dynamic-flow shape in the mini language:

> Callback flow is no longer only represented by an opaque summary in the mini
> slice.  Production event-loop ordering, async/await, promises, cancellation,
> reentrancy, lifecycle hooks, and framework callback discovery remain external
> obligations.

`PcSastLean.RichSourceProvenance` enriches source-backed report evidence:

- `SourceSpan`: start/stop source locations.
- `SourceOrigin`: direct, generated, macro-expansion, or template-expansion
  origin metadata.
- `RichSourceSinkProv`: source sink, artifact sink, AST node id, span, and
  origin.
- `RichSourceSinkProv.toBasic`: erases rich provenance to the smaller
  `SourceSinkProv` interface.
- `richSourceBackedRun_sound`: rich single-finding provenance can be consumed by
  the existing source-backed adapter theorem.
- `richMultiSourceBackedRun_sound`: the same result for multi-finding reports.
- `miniSinkRichProv_source_sink`: a mini source sink statement produces rich
  provenance with the expected source sink, artifact sink, AST node, and direct
  origin.
- `collectMiniRichProvs`: extracts rich provenance for every mini source sink
  statement.
- `collected_mini_rich_provs_cover_source_violations`: every mini source
  violation is covered by an extracted rich provenance certificate.
- `collected_mini_rich_provs_sound`: extracted rich provenance is sound against
  the compiled IR violation list.

This improves the report boundary without overclaiming:

> Lean can preserve, generate for the mini source language, and check structured
> source provenance.  A real extractor still has to prove that parser spans,
> source maps, generated code, macro expansion, and template expansion metadata
> are correct.

`PcSastLean.IFDS` adds an IFDS-style interprocedural dataflow layer:

- `IFDSNode`: an exploded-supergraph node containing procedure, program point,
  and dataflow fact.
- `IFDSEdge`: a fact-propagation edge with a `normal`, `call`, or `ret` action.
- `ValidActions`: a call/return stack discipline for valid interprocedural
  paths.
- `IFDSPath`: edge-by-edge reachability through the exploded supergraph.
- `checkIFDSCert`: a decidable certificate checker for a concrete path witness.
- `checked_ifds_cert_sound`: if the checker accepts the certificate, the target
  fact is reachable by a valid IFDS-style interprocedural path.

This does not yet implement the IFDS solver itself.  It verifies the solver's
finding artifact:

> A SAST engine can emit an exploded-supergraph path certificate, and Lean checks
> that the path uses real dataflow edges and respects call/return matching.

`PcSastLean.IFDSFixpoint` adds a no-finding certificate for IFDS-style solvers:

- `IFDSFixpointCert`: a finite set of reached exploded-supergraph nodes.
- `SeedsIncluded`: all IFDS seeds are in the reached set.
- `EdgeClosed`: every graph edge out of the reached set stays inside the reached
  set.
- `ifds_reachable_in_fixpoint`: any IFDS-reachable target is in a valid closed
  reached set.
- `checked_ifds_no_reach`: if the checker accepts the fixpoint certificate and a
  target is absent from the reached set, that target is not IFDS-reachable.

This is the solver-side complement to path certificates:

> Path certificates justify findings; closed fixpoint certificates justify
> no-finding claims.

`PcSastLean.IFDSSummary` adds summary-edge/tabulation-style certificates:

- `IFDSSummaryCert`: a reusable summary segment from one exploded-supergraph
  node to another, justified by raw IFDS hops.
- `checkIFDSSummary_sound`: an accepted summary certificate expands to an
  ordinary IFDS path with valid call/return actions.
- `IFDSSegment`: a compressed finding path segment, either a raw IFDS hop or a
  checked summary segment.
- `ifds_path_append`: ordinary IFDS paths compose.
- `checked_compressed_segments_to_path`: a checked compressed segment list
  expands to an ordinary IFDS path over the original graph.
- `IFDSCompressedCert` and `checked_ifds_compressed_cert_sound`: a compressed
  finding certificate is sound if its segments chain from a seed to a target and
  the overall call/return action sequence is valid.

This matches real IFDS solver artifacts more closely:

> A tabulation solver may emit summary segments instead of every raw edge.  Lean
> accepts the compressed finding only if each summary can be expanded back to
> checked IFDS hops and the whole expanded path has valid call/return discipline.

`PcSastLean.IFDSDistributive` adds the missing bridge back toward the original
Reps-Horwitz-Sagiv formulation:

- `IFDSFactFlow`: a sparse finite relation from input facts to output facts.
- `applyFactFlow`: the induced subset transformer over finite fact lists.
- `applyFactFlow_sound` and `applyFactFlow_complete`: membership in the
  transformer is exactly justified by relation edges whose source facts are in
  the input set.
- `applyFactFlow_append_distributes`: relational transfer distributes over
  list-union membership, matching the IFDS finite-distributive-subset premise in
  the union-confluence case.
- `IFDSFlowEdge`: a program-point edge carrying a sparse fact-flow relation.
- `explodeFlowEdge` and `explodeFlowGraph`: compile relation edges into ordinary
  exploded-supergraph edges.
- `flowHopsPath_to_IFDSPath` and `ifds_flow_path_cert_sound`: a valid relational
  flow-path certificate implies ordinary `IFDSReachable` after explosion.

This closes part of the earlier IFDS integration gap:

> The checker no longer starts only after an exploded graph magically exists.
> It now has a formal layer where finite distributive flow relations enter and
> are lowered to exploded-supergraph reachability.  What remains external is
> proving that real program statements emitted those relations, plus tabulation
> algorithm correctness and complexity.

`PcSastLean.CPG` adds a Code Property Graph / CodeQL / Joern style layer:

- `CPGNode`: typed graph nodes with source-location provenance.
- `CPGEdge`: typed graph edges such as AST, CFG, data dependence, control
  dependence, call, and return.
- `CPGPath`: a path through typed CPG edges.
- `CPGFindingCert`: a source-to-sink graph traversal witness.
- `checkCPGFinding`: a decidable checker that confirms the source/sink belong to
  the declared source/sink sets and every hop is a real CPG edge.
- `checked_cpg_finding_sound`: if the checker accepts, the source and sink are
  connected by a certified typed CPG path.

This verifies the artifact emitted by a graph-query SAST engine:

> A CodeQL/Joern-style engine can emit the concrete CPG path that made a query
> match; Lean checks that the path is real and source/sink-typed.

`PcSastLean.IFDSCPGEmbedding` relates the two certificate languages:

- `ifdsNodeId`: encodes IFDS exploded-supergraph nodes as CPG node ids.
- `ifdsActionKind`: maps IFDS `normal`, `call`, and `ret` actions to CPG
  `data`, `call`, and `ret` edge kinds.
- `ifdsGraphToCPGEdges` and `ifdsCPGNodes`: build a CPG-style graph from an IFDS
  exploded supergraph.
- `ifdsCertToCPGCert`: turns an IFDS path certificate into a CPG path
  certificate over the encoded graph.
- `checkCPGHops_of_checkHops`: an IFDS hop certificate accepted by the IFDS hop
  checker is accepted by the CPG hop checker after encoding.
- `ifds_cert_embeds_as_cpg_cert`: an accepted IFDS path certificate becomes an
  accepted CPG finding certificate over the encoded IFDS graph.

This is the precise relationship proved so far:

> IFDS is not equivalent to CPG.  But an accepted IFDS path certificate can be
> faithfully consumed as a CPG-style typed path certificate after encoding the
> exploded supergraph.

`PcSastLean.CPGProvenance` starts closing the next CPG trust boundary:

- `CPGEdgeCert`: a certificate for a CPG edge.
- `DataEdgeReason`: a toy provenance reason explaining why a data-dependence
  edge exists, such as source value, sanitizer flow, or sink use.
- `TypedCPGEdgeCert` and `CPGEdgeReason`: typed provenance for data, AST, CFG,
  control-dependence, call, and return CPG edges.
- `DataEdgeSoundForStmt`: the edge must correspond to the source statement's
  dataflow shape.
- `typed_edge_cert_kind_sound`: a typed edge certificate implies the CPG edge
  kind matches its stated reason.
- `CPGEdgesCertified`: every edge used by the CPG graph has a sound provenance
  certificate.
- `CPGHopsCertified`: every hop used by one finding certificate has a sound
  provenance certificate, without requiring provenance for unrelated graph
  edges.
- `checked_cpg_finding_path_provenance_sound`: if a CPG finding checks and every
  hop in that finding path has typed provenance, Lean returns both the graph
  finding and the path-specific provenance guarantee.
- `checked_cpg_finding_with_provenance_sound`: if a CPG finding checks and every
  edge has provenance, Lean returns both the graph finding and the provenance
  guarantee.

This separates two CPG claims:

> Path soundness: the query path is in the graph.
>
> Edge provenance soundness: each path hop came from a justified source-level or
> structural fact, and the provenance reason matches the CPG edge kind.

`PcSastLean.CPGConstruction` adds a small construction bridge for the
Yamaguchi-style CPG merge:

- `CPGComponentKind`: component edge kinds for AST, CFG, data dependence,
  control dependence, call, and return.
- `CPGComponentEdge.toCPGEdge`: lowers component edges into typed CPG edges.
- `mergeComponentEdges`: merges component edges into one CPG edge list.
- `component_edge_mem_merge`: every component edge appears in the merged graph.
- `componentPath`: paths over component graph edges.
- `componentPath_to_CPGPath`: component paths lift to ordinary CPG paths over
  the merged graph.
- `cpg_component_path_cert_sound`: a component-path certificate implies CPG
  reachability after merging.
- `component_path_hops_have_provenance`: each component path hop has preserved
  construction provenance.

This narrows the CPG gap:

> CPG is no longer only an assumed typed graph.  The verified slice now models a
> small merge from AST/CFG/PDG-style components into one CPG and proves path
> preservation across that merge.  What remains external is proving that those
> component edges correctly reflect real source syntax, control flow, and
> dependencies.

`PcSastLean.CPGTraversal` adds a tiny vulnerability-template layer over CPG
paths:

- `CPGKindFilter`: edge-kind filters for wildcard, exact kind, and one-of-many
  kind choices.
- `cpgHopsMatchFilters`: semantic relation between a concrete hop list and a
  filter sequence.
- `checkCPGHopsMatchFilters_sound`: an accepted filter check implies the
  semantic match relation.
- `CPGTraversalQuery`: a source set, sink set, and edge-kind filter sequence.
- `CPGTraversalMatch`: a query match is source/sink membership plus a real CPG
  path satisfying the filters.
- `checked_cpg_traversal_match_sound`: accepted traversal certificates imply
  `CPGTraversalMatch`.
- `checked_cpg_traversal_finding_sound`: accepted traversal certificates also
  imply ordinary `CPGFinding`.
- `checked_cpg_traversal_path_and_filters`: accepted traversal certificates
  produce a `CPGPath` and a proof that the path's edge kinds satisfy the query
  template.

This covers the second half of the CPG idea in miniature:

> Findings can now be checked as matches of a vulnerability traversal template,
> not merely as arbitrary source-to-sink paths.  The template language is still
> tiny: it has source/sink id sets and edge-kind filters, but no node-property
> predicates, joins, repetition, negation, or graph database semantics.

`PcSastLean.Feasibility` adds path-feasibility obligations:

- `BoolExpr`: a tiny symbolic Boolean language for path conditions.
- `Satisfies` and `Feasible`: semantic definitions for path-condition
  satisfiability.
- `UnsatWitness`: a simple unsatisfiability witness based on contradictory
  guards `p` and `not p`.
- `checkUnsatWitness_sound`: if the witness checker accepts, the path condition
  is infeasible.
- `unsat_finding_not_concrete_possible`: an infeasible path finding cannot be a
  concrete finding.
- `FeasibleSuppressionSound`: a suppression can be discharged by a feasibility
  witness.

This gives `SuppressionGate` a concrete witness language:

> A path can be suppressed as false positive when its path condition has a
> checked unsat witness.

`PcSastLean.SMTCore` adds a solver-shaped feasibility certificate:

- `UnsatCoreCert`: a list of clause indices plus a contradictory pivot.
- `getCoreClauses`: extracts the core clauses from the full path condition.
- `checkUnsatCore`: checks that the core contains both `p` and `not p`, and that
  both are real clauses of the path condition.
- `checkUnsatCore_sound`: if the core checker accepts, the path condition is
  infeasible.
- `unsat_core_finding_not_concrete_possible`: a finding with an accepted unsat
  core is not concrete-possible.

This is closer to how SMT-backed SAST triage works:

> The analyzer can attach an unsat core to an infeasible path; Lean checks the
> core before allowing suppression.

`PcSastLean.SMTResolution` adds a small propositional proof-step layer:

- `PropLit`: positive or negative propositional atoms.
- `implicationExpr`: encodes an implication step as a clause `not p or q`.
- `checkImplicationChain`: checks a chain of implication clauses in the path
  condition.
- `ResolutionChainCert`: starts from a unit literal, propagates through the
  implication chain, and contradicts the final negated unit.
- `checkResolutionChainUnsat_sound`: accepted resolution-chain certificates make
  the path condition infeasible.
- `resolution_chain_finding_not_concrete_possible`: resolution-chain evidence
  can discharge finding feasibility.

This narrows the SMT gap, while keeping the boundary clear:

> Feasibility evidence is no longer limited to a direct `p`/`not p` pivot.  It
> can now replay a small propositional implication chain.  Full SMT theory proof
> replay for arithmetic, equality, strings, arrays, regexes, bitvectors, and
> quantifiers remains external.

`PcSastLean.Framework` adds web-framework route extraction:

- `RouteKey`, `Request`, and `RouteEntry`: a tiny HTTP routing model.
- `resolveConcrete`: concrete routing selects one handler.
- `resolveAbstract`: framework extraction returns a may-set of handlers.
- `RouteExtractionSound`: the concrete handler must be included in the abstract
  may-set.
- `HandlerSound`: concrete handler violations are covered by abstract handler
  summaries.
- `framework_route_sound`: request-level concrete violations are covered by the
  route-level abstract result.
- `framework_fix_gate` and `framework_baseline_gate`: fix/baseline gates lifted
  to web requests.

This turns framework modeling into a checkable obligation:

> If route extraction misses a concrete handler, request-level safety cannot be
> claimed.  If every concrete handler is in the may-route set, handler-level
> SAST claims lift to request-level claims.

`PcSastLean.FrameworkTemplate` adds literal/parameter path templates:

- `PathSegment`: either a literal path atom or a parameter segment.
- `templateMatches`: checks whether a path matches a template.
- `TemplateRoute` and `TemplateRequest`: toy framework routes with method and
  path segments.
- `resolveTemplateConcrete`: concrete first-match route resolution.
- `resolveTemplateAbstract`: abstract may-route extraction returning every
  matching handler.
- `template_route_extraction_sound`: the concrete first-match handler appears in
  the abstract may-route set.
- `template_framework_sound`: handler soundness lifts to template-routed
  requests.
- `template_framework_fix_gate`: if the abstract template route result excludes
  a sink, the concrete template route result excludes it too.

The precision lesson is explicit:

> Parameter routes can over-approximate concrete first-match routing.  This is
> sound, but may introduce false positives when a more specific literal route
> shadows a parameter route.

`PcSastLean.FrameworkShadowSuppression` proves a concrete route-shadow
suppression theorem:

- `RouteShadowEvidence`: a request, concrete first-match handler, shadowed
  abstract handler, and sink.
- `checkRouteShadowEvidence`: checks that concrete routing selects the concrete
  handler, the shadowed handler is in the abstract may-set, the two handlers are
  different, and the selected concrete handler does not contain the sink.
- `checked_route_shadow_not_concrete`: accepted route-shadow evidence proves the
  sink is absent from concrete request execution.
- `routeShadowTriageEvidence_sound`: route-shadow evidence can serve as
  proof-carrying triage evidence.
- `shadowTriageComplete`: a demo where a shadowed parameter-route finding is
  suppressed while the final report still covers every concrete bug.

This is a deliberately more useful precision theorem:

> A may-route abstraction can introduce a false positive; concrete first-match
> route evidence can remove that false positive without weakening
> no-bug-hiding.  The evidence is not merely "the sink is absent"; it is checked
> route-resolution structure that implies absence.

`PcSastLean.Middleware` adds middleware/auth guard extraction:

- `Role`, `Principal`, and `Guard`: a small authorization model.
- `guardsAllow`: a guard-chain evaluator.
- `GuardChainIncluded`: extracted abstract guards must be included in the
  concrete guard chain for the over-approximation direction used here.
- `guardsAllow_subset`: if the concrete guard chain allows a request, the
  included abstract guard chain also allows it.
- `guarded_framework_sound`: route extraction, guard extraction, and handler
  summary soundness imply guarded request-level soundness.

The important negative lesson is also encoded in the design:

> "Abstract guard blocks" does not imply "concrete guard blocks" unless the
> concrete guard is known to exist.  Guard-based suppression still needs a
> concrete feasibility witness.

`PcSastLean.Template` adds template rendering contexts:

- `TemplateContext`: HTML text, HTML attribute, JavaScript string, and URL
  attribute contexts.
- `TemplateSlot`: a rendered value, its template context, and its sink id.
- `TemplateContext.requiredSink`: maps each slot context to the sanitizer
  capability required by the context-sensitive lattice.
- `renderTemplate`: reports a violation when a value lacks the required
  capability for its slot.
- `html_sanitizer_not_url_safe`: HTML sanitization does not prove URL-attribute
  safety.

This is the XSS-specific version of the sanitizer lattice:

> A value is not globally template-safe.  It is safe only for the slot contexts
> whose required capabilities it carries.

`PcSastLean.ORM` adds SQL query construction semantics:

- `QueryPart`: literal SQL fragments, concatenated values, and prepared
  parameter values.
- `queryPartViolation`: concatenating a value into SQL requires SQL protection;
  binding a value as a prepared parameter does not.
- `prepared_param_no_violation`: prepared parameters do not create SQLi
  violations in this model.
- `concat_value_safe_if_sql_safe`: string concatenation is safe only when the
  value has SQL protection.
- `concat_value_violation_if_not_sql_safe`: string concatenation of unprotected
  input produces a SQLi violation.

This separates two common SQLi defenses:

> SQL sanitization makes string concatenation safe.  Prepared binding avoids
> string concatenation risk by construction.

`PcSastLean.AllocationSite` adds allocation-site heap abstraction:

- `ConcreteAllocHeap`: concrete variables point to concrete objects, and each
  object has an allocation site.
- `AbsAllocHeap`: abstract points-to sets contain allocation sites rather than
  concrete object ids.
- `AllocHeapSound`: concrete variable labels, points-to sites, and heap fields
  are covered by the allocation-site abstraction.
- `readAbsAllocField_sound`: reading a concrete object field is covered by
  joining abstract fields over its may allocation sites.
- `alloc_writeMayField_sound`: concrete object field writes are covered by
  abstract writes to the corresponding may allocation sites.

This is the pointer-analysis bridge:

> Multiple concrete objects can be collapsed into allocation sites while
> preserving heap-taint soundness.

`PcSastLean.ObjectSensitive` adds object-sensitive/context-sensitive heap keys:

- `ObjSensKey`: allocation site plus context key.
- `AbsObjSensHeap`: variables point to object-sensitive keys, and heap facts are
  stored per key.
- `ObjSensHeapSound`: concrete heap facts are covered by object-sensitive heap
  facts.
- `projectObjSensHeap`: projects object-sensitive facts back to an
  allocation-site heap by joining over contexts.
- `object_sensitive_projects_to_alloc_sound`: if the object-sensitive heap is
  sound and covers concrete objects, its projection is a sound allocation-site
  abstraction.

This connects precision and soundness:

> Object-sensitive analysis refines allocation-site analysis.  Joining over
> contexts recovers a sound context-insensitive abstraction.

`PcSastLean.PointerArithmetic` adds a base+offset pointer abstraction:

- `OffsetPtr`: a toy pointer made of a base id and natural offset.
- `ConcreteOffsetHeap`: one exact offset pointer per variable.
- `AbsOffsetHeap`: a may-set of offset pointers per variable.
- `OffsetHeapSound`: variable taints, concrete pointer membership, and memory
  labels are covered by the abstract state.
- `offset_ptr_add_sound`: concrete pointer addition is covered by mapping the
  same offset addition over the abstract may-pointer set.
- `readAbsPtr_sound`: reading through a concrete offset pointer is covered by
  joining memory facts over all abstract may-pointers.
- `offset_writeMayPtr_sound`: concrete writes through an exact offset pointer are
  covered by may-writes over all abstract candidate pointers.
- `offset_load_sound`: loading from memory through an offset pointer preserves
  abstract soundness.

This narrows the pointer-arithmetic gap, but only in a small model:

> Base+offset pointer arithmetic can be verified as a may-alias abstraction.
> Production C/C++ pointer provenance, byte layout, undefined behavior, unsafe
> casts, negative offsets, concurrency, and native memory APIs remain outside the
> model.

`PcSastLean.PointerDisjointSuppression` proves a targeted alias false-positive
suppression theorem:

- `concreteWriteLoadSink`: a concrete write-through-pointer, load-through-pointer,
  and sink sequence.
- `abstractWriteLoadSink`: the matching abstract sequence where may-alias writes
  can taint more memory locations than the concrete execution.
- `pointer_disjoint_write_load_not_concrete`: if the concrete write pointer and
  read pointer are different and the concrete read target is clean, the sink is
  absent from concrete execution.
- `checkPointerDisjointEvidence_sound`: the Boolean evidence checker implies the
  trusted pointer-disjointness proposition.
- `checked_pointer_disjoint_not_concrete`: checked disjointness evidence proves
  the may-alias finding is not concrete.
- `pointerDisjointTriageComplete`: a demo where the abstract may-alias run reports
  a finding, concrete execution does not, and proof-carrying triage suppresses
  the finding without weakening the CI no-bug-hiding theorem.

This is the alias analogue of route-shadow suppression:

> A sound may-alias abstraction can introduce false positives.  Concrete
> base+offset disjointness evidence can remove one such false positive without
> appealing directly to "the sink is absent."  The production burden is now clear:
> real extractors must justify that the pointers are genuinely disjoint under the
> source language's memory model.

`PcSastLean.NoBugHiding` adds the deepest triage theorem so far:

- `TriageEvidence`: evidence attached to a suppressed sink.
- `EvidenceSound`: evidence proves the suppressed sink is absent from concrete
  violations.
- `TriageComplete`: every abstract finding is either reported or suppressed with
  sound evidence.
- `no_bug_hiding`: if concrete bugs are included in abstract findings and triage
  is complete, every concrete bug is still reported.
- `no_bug_hiding_not_reported`: anything not in the report is not a concrete bug.
- `evidenceFromUnsatFinding`: an SMT-core-backed infeasibility finding can serve
  as triage evidence.

This is the proof-carrying triage theorem:

> A SAST team may suppress false positives, but only with evidence strong enough
> to prove that the suppressed sink is not concrete.  Under that discipline,
> triage cannot hide real bugs.

`PcSastLean.CIGate` packages the theory as a CI-facing interface:

- `AnalyzerRun`: concrete and abstract violation lists for one analyzer family.
- `AnalyzerRun.Sound`: concrete violations are included in abstract violations.
- `TriageRun`: final report, suppressed findings, and evidence.
- `TriageRun.Complete`: every abstract finding is reported or soundly
  suppressed.
- `ci_gate_no_bug_hiding`: if the analyzer run is sound and triage is complete,
  every concrete bug is in the final report.
- `ci_gate_not_reported_not_concrete`: if a sink is absent from the report, it is
  absent from concrete bugs.
- adapters for heap, sanitizer, and framework analyzer runs.

This is the top-level theorem:

> A CI SAST gate is trustworthy when every analyzer run is sound and every
> suppression is proof-carrying.  Then the final report cannot omit a concrete
> bug from the modeled analyzer family.

`PcSastLean.MultiAnalyzer` lifts the CI gate to multiple analyzer families:

- `aggregateRuns`: unions concrete and abstract findings from a list of analyzer
  runs.
- `aggregateRuns_sound`: if every analyzer run is sound, the aggregate run is
  sound.
- `aggregate_ci_gate_no_bug_hiding`: if every analyzer is sound and aggregate
  triage is complete, the aggregate final report contains every concrete bug.

This matches real SAST CI:

> Heap, sanitizer, framework, IFDS, and CPG analyzers can feed one report.  The
> combined report remains no-bug-hiding when each analyzer soundness certificate
> and the combined triage certificate are checked.

`PcSastLean.CertificateAdapters` connects proof-carrying certificates to CI runs:

- `ifdsTargetSink`: deterministically projects an IFDS exploded-supergraph target
  node to the artifact sink reported to CI.
- `IFDSSinkProjection.Sound`: the projection object must match the checked IFDS
  certificate target and sink projection.
- `ifdsFindingRun`: turns an accepted IFDS path certificate plus a sound target
  projection into an analyzer run.
- `ifdsFindingRun_reports_only_target_sink`: the IFDS adapter cannot report an
  arbitrary external sink; every reported sink is the sink projected from the
  checked certificate target.
- `ifdsCompressedFindingRun`: lifts accepted compressed IFDS summary/path
  certificates into analyzer runs.
- `ifdsCompressedFindingRun_reports_only_target_sink`: compressed IFDS reports
  obey the same target-projection discipline.
- `ifdsNoFindingRun`: turns an accepted IFDS fixpoint/no-reach certificate into
  an empty analyzer run for that absent target.
- `cpgFindingRun`: turns an accepted CPG path certificate into an analyzer run
  whose sink is the checked certificate sink, not an external report id.
- `cpgFindingRun_reports_only_cert_sink`: the CPG adapter has the same
  no-external-sink property.
- adapter soundness theorems show these generated runs satisfy
  `AnalyzerRun.Sound`.

This closes the loop between low-level certificates and the top-level CI gate:

> IFDS and CPG certificates can now participate in the same no-bug-hiding final
> report theorem as heap, sanitizer, and framework analyses, without letting the
> adapter swap a checked low-level finding for an unrelated report sink.

`PcSastLean.SourceBackedAdapters` adds source-level provenance to those adapters:

- `SourceSinkProv`: a checked link from an artifact-level sink to a source-level
  sink and source location.
- `SourceSinkProv.Sound`: if the source-level violation exists, the linked
  artifact-level violation must exist.
- `SourceViolationsCoveredBy`: the source finding set is covered by the
  provenance certificate.
- `SourceBackedRun`: remaps accepted artifact-level analyzer results into
  source-level CI findings.
- `sourceBackedAbstract`: remaps only provenance links whose artifact sink
  appears in the artifact-level abstract analyzer result.
- `SourceViolationsCoveredByAny` and `SourceProvsSound`: list-level provenance
  obligations for multi-finding reports.
- `MultiSourceBackedRun`: lifts a whole artifact analyzer run through a list of
  source/artifact provenance links.
- `sourceBackedRun_sound`, `sourceBackedIFDSRun_sound`, and
  `sourceBackedCPGRun_sound`: artifact analyzer soundness plus provenance
  soundness imply source-level analyzer soundness.
- `multiSourceBackedRun_sound`: if every source violation is covered by some
  sound provenance link and the artifact analyzer is sound, then the remapped
  multi-finding source-level run is sound.

This closes the adapter-level version of the extraction gap:

> A low-level IFDS/CPG certificate is not enough by itself to enter the
> source-level CI report.  It must carry provenance that ties the artifact sink
> back to a source sink and location.  For multi-finding reports, every reported
> source violation must be covered by one of these sound provenance links.

`PcSastLean.AssumptionLedger` records the claim boundary explicitly:

- `ModeledSurface`: the surfaces currently modeled by the repository, such as
  toy expression taint, linear IR, heap may-aliasing, sanitizer capabilities,
  IFDS/CPG certificates, and CI triage.
- `ExternalObligation`: obligations not yet discharged here, including
  real-language extraction, dynamic summary soundness, richer SMT theories, CPG
  extraction provenance, and precision evaluation.
- `SourceLevelGateInputs`: the input bundle required for a source-level CI
  no-bug-hiding claim.  It includes `SourceToIRSound`, analyzer soundness, and
  complete proof-carrying triage.
- `source_level_ci_no_bug_hiding`: source-level no-bug-hiding follows only from
  those inputs.

This makes the non-vacuity condition explicit:

> Without an extraction certificate and analyzer/triage obligations, the
> source-level CI theorem is not available.

This is deliberately a verified slice rather than a full scanner.  The current
trusted claim is:

> For the modeled toy languages and certificate formats, Lean verifies
> conditional soundness and no-bug-hiding theorems: accepted certificates imply
> trusted graph/path/fixpoint facts; abstract executions over-approximate
> corresponding concrete toy executions; proof-carrying triage cannot hide a
> concrete modeled bug; targeted structural evidence can suppress route-shadow
> and pointer-disjoint false positives; and source-level CI claims require
> explicit extraction and provenance obligations.  The repository does not yet
> verify extraction from a production language or prove general precision
> improvements.

The current unverified gap is extraction from real languages into this IR.

## Next Formalization Steps

1. Extend source-backed adapters from list-level source/artifact links to richer
   extraction certificates over source spans, AST nodes, and generated-code
   artifacts.
2. Extend object-sensitive keys to call strings and receiver-type sensitivity.
3. Extend framework modeling to middleware order and transaction/query-builder
   APIs.
4. Refine template contexts for nested HTML/JS/CSS/URL parser states.
5. Replace the toy contradictory-pivot core with richer SMT proof certificates
   for equalities, arithmetic, strings, and theory lemmas.
6. Add CPG node-property predicates for call names, argument positions, source
   classifications, and sink classifications.
7. Extend CPG provenance from toy data edges to real AST/CFG/DDG/CDG extraction
   rules.
8. Refine pointer-disjoint suppression with byte ranges, object bounds, and
   provenance-aware no-overlap certificates.
9. Add relational IFDS fixpoint/no-reach certificates over `IFDSFlowEdge`, not
   only already-exploded `IFDSEdge`.
10. Add IFDS summary-edge fixpoint/no-reach certificates, not only compressed
   finding certificates.
11. Build real extractors that emit `SourceToIRSound` certificates for a target
   language or framework.
12. Add real feasibility witnesses from SMT, runtime traces, or fuzzer witnesses.
13. Lift `SanitizerLattice` labels into the heap and procedure-summary modules.
14. Split concrete execution from abstract execution so the analyzer can be less
   precise while remaining sound.
15. Add sanitizer obligations as proof-producing predicates.
16. Export a simple JSON certificate format from a toy scanner.
17. Build a Lean-side parser/checker for that certificate format.
18. Prove source-language extraction preserves the security-relevant semantics.

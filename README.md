# pc-sast-lean

Proof-carrying SAST research scaffold.

This repository experiments with a Lean verification layer for SAST output.  The
goal is not to rewrite an entire scanner in Lean, but to let practical scanners
emit certificates that Lean can check.

Current scope and non-claims:

- The executable IR is intentionally small.  It models taint, simple heap fields,
  procedure summaries, sanitizer capabilities, IFDS/CPG certificates, and CI
  triage gates.  It models only toy base+offset pointer arithmetic, not
  production pointer provenance or byte layout.  It does not yet model async
  scheduling, callbacks, exception flow, reflection, or build-system semantics.
- Source-level claims are conditional on extraction certificates such as
  `SourceToIRSound`.  Real-language extraction is not implemented here yet.
- Dynamic/framework behavior is represented by soundness obligations and toy
  route/guard models, not by a production framework semantics.
- SMT/path feasibility is currently a small Boolean contradiction-core checker,
  not a checker for LRA, EUF, strings, arrays, regexes, or theory lemmas.
- Object sensitivity currently proves projection from abstract context keys to
  allocation-site abstraction; it does not yet encode real call-string-k or
  receiver-type sensitivity.
- CPG provenance includes typed path-hop certificates, but real AST/CFG/DDG/CDG
  extraction rules are still future work.
- The main result is soundness/no-bug-hiding under stated obligations.  Precision
  and false-positive reduction are not general proved properties, though there
  are targeted conditional precision theorems such as route-shadow and
  pointer-disjoint suppression.

Claim boundary:

| Area | Status | What is proved | What is not proved |
| --- | --- | --- | --- |
| Toy taint/IR semantics | Verified | Soundness for modeled taint, branches, summaries, heap fields, and sanitizer labels | Production language semantics |
| Mini source extraction | Verified | A separate mini source AST compiles exactly to the sanitizer IR and yields `SourceToIRSound` | Real TypeScript/Python/Java extraction |
| Mini source branches | Verified | Concrete source branch execution is covered by abstract branch/join execution | Real CFG construction, path feasibility, exceptions, callbacks, async |
| Mini source exceptions | Verified | Concrete mini try/catch/finally execution is covered by abstract handler/join execution | Stack unwinding, typed exceptions, promises, async rejection paths |
| Mini source callbacks | Verified | Optional concrete callback execution is covered by abstract execution that includes the callback path | Event-loop ordering, async/await, promise chains, reentrancy |
| Rich source provenance | Conditional | Source spans, AST node ids, generated-code origins, and mini extractor-generated provenance lists erase safely to source-backed adapter proofs | Correct real source maps, parser spans, macro/template expansion provenance |
| Offset pointer arithmetic | Conditional toy model | Base+offset pointer add/read/write preserve may-alias soundness | C/C++ pointer provenance, byte layout, UB, unsafe casts, negative offsets |
| IFDS/CPG certificates | Verified/conditional | Accepted path/fixpoint/summary certificates imply trusted graph facts; sparse IFDS fact-flow relations lower to exploded graph paths | That a real extractor built the graph correctly |
| CI no-bug-hiding | Conditional | Sound analyzer run plus complete proof-carrying triage cannot hide modeled bugs | Source-level safety without extraction/provenance |
| Production source extraction | External obligation | Transfer theorems once `SourceToIRSound` is supplied | Full real-language semantics and parser/source-map correctness |
| SMT feasibility | Conditional toy model | Boolean contradiction cores and propositional implication-chain resolution | LRA, EUF, strings, arrays, regex theory proofs |
| Framework/dynamic behavior | Conditional toy model | May-route/guard/summary obligations and literal/param route-template extraction compose soundly | Full framework dispatch, regex routing, content negotiation, async, callbacks, exceptions |
| Route-shadow suppression | Conditional precision theorem | First-match route evidence can soundly suppress a shadowed parameter-route false positive | Full framework precedence, regex/converter constraints, middleware interactions |
| Pointer-disjoint suppression | Conditional precision theorem | Concrete base+offset disjointness can soundly suppress an abstract may-alias false positive | Real C/C++ provenance, byte layout, UB, unsafe casts, partial overlap, concurrency |
| General precision | Not modeled | Targeted conditional suppressions only | Broad FP reduction or recall/precision guarantees |

Current verified slice:

- graph-level source-to-sink certificate checking;
- a tiny executable Security IR with `source`, `assign`, `sanitize`, and `sink`;
- store soundness theorems for taint propagation;
- violation-subset soundness for abstract execution;
- concrete finding and safety certificate soundness.
- an abstract safety gate: accepted abstract safety implies concrete safety when
  the abstract store over-approximates the concrete store.
- branch/join soundness: concrete branch execution is covered by abstract
  execution that analyzes both sides and joins results.
- procedure-summary soundness for interprocedural calls.
- parameter/return-aware procedure summaries of the form
  `argument taints -> return taint + violations`.
- heap/object-field soundness with may-points-to sets and precise may-target
  field writes.
- baseline-gated CI theorems: if abstract findings are covered by an approved
  baseline, concrete execution has no new violation outside that baseline.
- verified fix gates: if a patched abstract run removes a specific sink, the
  patched concrete run cannot contain that sink.
- dynamic obligations: fix/baseline gates remain valid for dynamic calls only
  when runtime/framework/config witnesses provide sound summaries.
- context-sensitive sanitizer lattice: SQL, HTML, shell, and path protections are
  tracked separately, so the wrong sanitizer cannot prove sink safety.
- sanitizer-aware soundness and fix gate: abstract sanitizer analysis cannot
  remove a concrete sink by claiming protections the concrete value lacks.
- proof-carrying suppression gate: false positives can be hidden only with an
  obligation proving the concrete violation cannot occur.
- source-to-IR extraction gates: IR-level safety/fix/baseline claims transfer
  back to source only with an extraction soundness certificate; real extractors
  are still an external obligation.
- mini source-language extraction: a separate source AST and source semantics
  compile exactly to the sanitizer IR and produce `SourceToIRSound`.
- mini source branch/join soundness: concrete source branch execution is covered
  by abstract source branch execution that analyzes both branches and joins.
- mini source exception-flow soundness: concrete try/catch/finally execution is
  covered by abstract execution that analyzes protected and handler paths.
- mini source callback-flow soundness: optional concrete callback execution is
  covered by abstract execution that includes the possible callback path.
- rich source provenance: source spans, AST node ids, and generated-code origins
  can be carried through source-backed adapter soundness; the mini extractor
  also generates provenance lists covering source violations.
- IFDS-style valid-path certificates over an exploded supergraph with
  call/return matching.
- IFDS fixpoint/no-finding certificates: accepted closed reachable sets prove
  absent targets are not IFDS-reachable.
- IFDS summary-edge/compressed finding certificates: accepted compressed paths
  expand to ordinary IFDS paths over the original graph.
- IFDS finite-distributive flow bridge: sparse fact-flow relations distribute
  over set-union membership and compile to ordinary exploded-supergraph paths.
- CPG/CodeQL-style source-to-sink graph path certificates over typed AST/CFG/DDG
  style edges with source-location provenance.
- IFDS-to-CPG embedding: accepted IFDS path certificates become accepted
  CPG-style path certificates over an encoded exploded supergraph.
- CPG edge provenance certificates, including path-specific typed provenance for
  data, AST, CFG, control, call, and return edges.
- path-feasibility suppression witnesses using a small checked Boolean
  path-condition language.
- SMT-style unsat-core certificates for infeasible path suppression.
- propositional resolution-chain feasibility certificates, so toy SMT evidence
  can go beyond a direct `p`/`not p` pivot.
- framework route-extraction gates: request-level claims require concrete
  handlers to appear in extracted may-route sets.
- framework route templates: literal/parameter path templates resolve concrete
  first-match routes into abstract may-route sets soundly.
- route-shadow suppression: a checked first-match route witness can suppress a
  shadowed abstract parameter-route finding without hiding a concrete bug.
- pointer-disjoint suppression: checked concrete offset-pointer disjointness can
  suppress an abstract may-alias false positive without hiding a concrete bug.
- middleware/auth guard extraction: guarded request soundness, with the caveat
  that guard-based suppression still needs concrete feasibility evidence.
- template rendering contexts: HTML text, attribute, JavaScript string, and URL
  attribute slots require different sanitizer capabilities.
- ORM/query construction semantics: prepared parameters are safe by construction,
  while string concatenation requires SQL protection.
- allocation-site heap abstraction for pointer-analysis style object merging.
- object-sensitive heap keys that project soundly back to allocation-site
  abstraction.
- offset pointer arithmetic: base+offset pointer addition and may-pointer
  reads/writes preserve abstract heap soundness in a toy model.
- no-bug-hiding triage theorem: complete proof-carrying suppressions cannot hide
  concrete bugs from the final report.
- top-level CI gate wrappers for analyzer soundness plus complete triage.
- multi-analyzer aggregation: sound analyzer runs can be unioned into one
  no-bug-hiding CI report.
- IFDS/CPG certificate adapters that lift accepted low-level certificates into
  top-level analyzer runs; reports are tied to checked IFDS target projections
  or the checked CPG certificate sink.
- source-backed certificate adapters: low-level artifact sinks can become
  source-level CI findings only with checked source-location provenance.
- multi-finding provenance lifting: a source-level report is sound when every
  source violation is covered by a sound source/artifact provenance link and the
  artifact analyzer run is sound.
- an explicit assumption ledger: source-level CI claims require extraction,
  analyzer soundness, and complete proof-carrying triage as inputs.
- module-level claim-boundary comments on the main proof layers, recording what
  is verified, what is an external obligation, and what is not modeled.

See `docs/THEORY.md` for the design notes.

Build:

```powershell
lake build
```

Run:

```powershell
lake exe pc_sast_lean
```

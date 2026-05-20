# Iteration 010: CPG Extraction-Origin Provenance

Paper thread:

- Continues Yamaguchi, Golde, Arp, and Rieck, "Modeling and Discovering
  Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- Primary paper PDF: <https://www.ieee-security.org/TC/SP2014/papers/ModelingandDiscoveringVulnerabilitieswithCodePropertyGraphs.pdf>
- Joern CPG specification: <https://cpg.joern.io/>

## Core Claim

The CPG paper's central move is to merge AST, CFG, and PDG-style relations into
one graph so vulnerability templates can be written as graph traversals.  That
creates a trust-boundary question for proof-carrying SAST:

> If a finding path uses a CPG hop, why should that hop be trusted?

This iteration adds an extraction-origin layer.  A hop is no longer only a typed
edge in the merged graph; it can be checked against an origin certificate saying
whether it came from AST, CFG, DDG, CDG, call, or return extraction.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPG`: checked source-to-sink paths over typed CPG edges.
- `PcSastLean.CPGProvenance`: path-specific typed edge provenance.
- `PcSastLean.CPGConstruction`: component AST/CFG/PDG/call/return edges merge
  into CPG edges, preserving paths.

Gap before this iteration:

- Component edges still appeared as trusted inputs.
- The checker could prove a component edge was preserved by merge, but not that
  the component edge had a typed extraction origin.
- The `cpgExtractionProvenance` obligation was too coarse: it did not separate
  orphan-edge prevention from correctness of real extraction algorithms.

## Lean Patch

Added `PcSastLean.CPGExtractionProvenance`.

New artifacts:

- `CPGExtractionOrigin`: AST child, CFG step, DDG reaching definition, CDG
  control dependence, call link, and return link origin facts.
- `CPGExtractionOrigin.toComponentEdge`: the component edge induced by an
  origin fact.
- `CPGExtractedEdgeCert.Sound`: the certificate's component edge must equal the
  origin-induced component edge.
- `checkCPGExtractedEdgeCert_sound`: boolean checking implies certificate
  soundness.
- `extracted_edge_kind_forced_by_origin`: the edge kind is forced by the origin
  class.
- `ExtractedHopCertified` and `ExtractedHopsCertified`: every CPG path hop can
  be required to have an extraction certificate.
- `checkExtractedHop_sound` and `checkExtractedHops_sound`: checker soundness
  for per-hop extraction provenance.
- `extracted_hop_has_origin_edge`: every certified hop lowers from a typed
  extraction origin to exactly the hop edge.
- `checked_cpg_finding_with_extraction_provenance_sound`: accepted CPG finding
  plus checked hop provenance yields the finding and origin-backed evidence for
  every hop.

## What This Improves

This iteration splits the CPG extraction gap into two smaller obligations:

1. Lean now checks that each finding-path hop has a typed extraction origin.
2. Production extractors still have to prove those origin facts are correct for
   real parser, CFG, DDG, CDG, call, and return-flow construction.

That is a better engineering contract.  A scanner cannot simply emit a
convenient synthetic edge and rely on the path checker.  It must also explain
which extraction layer produced that edge.

## Remaining Gaps

- The origin facts themselves are not derived from a real source-language
  semantics yet.
- DDG reaching definitions carry only a toy variable id, not alias-sensitive
  memory provenance.
- CFG/CDG construction algorithms are not verified.
- Interprocedural call/return origins are links, not summaries or call-stack
  balanced paths.
- Source spans and generated-code provenance are not yet tied into this CPG
  origin layer.

## Next Theorem Candidate

The next useful theorem is probably a no-orphan-edge adapter:

- require CPG traversal, node predicate, policy, sanitizer, and triage
  certificates to carry extraction-origin coverage for every hop;
- show the top-level CPG analyzer run cannot depend on a hop that lacks
  extraction provenance.

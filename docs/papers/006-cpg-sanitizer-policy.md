# Iteration 006: CPG Sanitizer Policy and Sanitizer Lattice

Paper thread:

- Continues the CPG line from Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

Practical CPG SAST queries often reason about sanitizers: a path from source to
sink may be acceptable only when an intermediate sanitizer protects the value for
the sink's required context.

Earlier iterations connected CPG findings to source/sink policy.  This iteration
connects CPG sanitizer facts to the existing context-sensitive
`SanitizerLattice`.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGPolicyProvenance`: endpoint source/sink classes are backed by
  policy rules.
- `PcSastLean.CPGNodePredicates`: traversal matches can require node facts.
- `PcSastLean.SanitizerLattice`: sanitizers grant context-specific
  `SinkKind` protections.

Gap before this iteration:

- A CPG traversal could mention node facts, but sanitizer facts were not tied to
  sanitizer policy.
- A sink class did not declare which `SinkKind` protection it requires.
- CPG query evidence did not connect to `SecLabel.sanitize_safe_for`.

## Lean Patch

Added `PcSastLean.CPGSanitizerPolicy`.

New artifacts:

- `CPGSanitizerPolicyRule`: sanitizer call-name rules and sink-class required
  `SinkKind` rules.
- `CPGSanitizerFactCert`: a certificate that a specific node is a sanitizer for
  one `SinkKind`.
- `checkCPGSanitizerFactCert_sound`: accepted sanitizer fact certificates imply
  trusted sanitizer-policy semantics.
- `SinkPolicyRequires`: a sink policy class requires a specific `SinkKind`.
- `SanitizerCoversFinding`: the sanitizer node appears on the finding path and
  provides the required `SinkKind`.
- `cpg_sanitizer_grants_required_protection`: bridge theorem to
  `SecLabel.sanitize_safe_for`.
- `CPGSanitizedTraversalCert`: policy-backed CPG finding plus sanitizer evidence.
- `CPGSanitizedTraversalMatch`: policy-backed traversal match plus sanitizer
  evidence and sanitizer-lattice protection.
- `checked_cpg_sanitized_traversal_sound`: accepted sanitizer-backed traversal
  certificates imply `CPGSanitizedTraversalMatch`.
- `checked_cpg_sanitized_finding_sound`: accepted sanitizer-backed traversal
  certificates still imply ordinary `CPGFinding`.

## What This Improves

The CPG query chain now reaches the sanitizer lattice:

1. Source/sink endpoint classes are backed by policy rules.
2. Sink classes declare a required `SinkKind`.
3. Sanitizer call names declare which `SinkKind` they provide.
4. A sanitizer node must occur on the finding path.
5. Lean proves that applying that sanitizer grants the required protection.

This prevents the theory from treating "sanitized" as a global Boolean.  The
sanitizer must match the sink context.

## Remaining Gaps

- Path order is only approximated by membership in hop destinations; dominance or
  before-sink ordering is not yet modeled.
- No proof that the sanitizer is applied to the same value that flows to the
  sink.
- No multi-argument sanitizer semantics.
- No parser-state sanitizer models for nested HTML/JS/CSS/URL contexts.
- No integration yet with suppression/no-finding gates for sanitized paths.

## Next Theorem Candidate

Add an ordered path sanitizer theorem:

- the sanitizer node must occur before the sink on the path;
- the data-dependence segment after the sanitizer must carry the sanitized value;
- only then can the sanitizer evidence suppress or discharge a CPG finding.

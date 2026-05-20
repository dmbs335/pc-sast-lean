# Iteration 008: CPG Sanitizer Evidence as Proof-Carrying Triage

Paper thread:

- Continues the CPG line from Yamaguchi, Golde, Arp, and Rieck, "Modeling and
  Discovering Vulnerabilities with Code Property Graphs", IEEE S&P 2014.
- DOI/metadata: <https://doi.org/10.1109/SP.2014.44>

## Core Claim

Sanitizer evidence is useful operationally only if it can affect triage without
hiding real bugs.  Earlier iterations proved that ordered sanitizer evidence is
well-formed.  This iteration packages that evidence into the proof-carrying
triage gate.

## Mapping to This Repository

Already covered before this iteration:

- `PcSastLean.CPGOrderedSanitizer`: sanitizer precedes sink and carries the same
  value token.
- `PcSastLean.CPGSanitizerPolicy`: sanitizer evidence connects to
  `SanitizerLattice`.
- `PcSastLean.CIGate` and `PcSastLean.NoBugHiding`: proof-carrying suppressions
  cannot hide concrete modeled bugs.

Gap before this iteration:

- Ordered sanitizer evidence did not yet produce `TriageEvidence`.
- The CPG sanitizer chain did not yet compose with `ci_gate_no_bug_hiding`.
- There was no explicit modeled concrete semantics for "this CPG sink is not a
  vulnerability because the required sanitizer is present."

## Lean Patch

Added `PcSastLean.CPGSanitizerTriage`.

New artifacts:

- `cpgUnsanitizedConcreteFinding`: a deliberately narrow modeled concrete
  semantics where a CPG sink is concrete only when checked ordered sanitizer
  evidence is absent.
- `checked_ordered_sanitizer_not_concrete`: accepted ordered sanitizer evidence
  proves the sink is absent from that modeled concrete finding list.
- `orderedSanitizerTriageEvidence`: converts ordered sanitizer evidence into
  `TriageEvidence`.
- `orderedSanitizerTriageEvidence_sound`: sanitizer evidence is sound for the
  modeled concrete CPG semantics.
- `orderedSanitizerRun`: analyzer run with sanitized concrete semantics and the
  abstract CPG finding.
- `orderedSanitizerRun_sound`: the sanitized concrete run is covered by the
  abstract finding set.
- `orderedSanitizerDemoTriageComplete`: a suppressed CPG finding is complete
  because it carries sanitizer evidence.
- CI demo: `ci_gate_no_bug_hiding` proves the final empty report hides no modeled
  concrete bug.

## What This Improves

The CPG sanitizer story now reaches the top-level CI theorem:

1. CPG path and traversal evidence establish the finding.
2. Source/sink policy provenance establishes endpoint classes.
3. Sanitizer policy and ordered value-flow evidence establish protection.
4. That evidence becomes proof-carrying suppression.
5. CI no-bug-hiding still holds.

This is the first CPG-specific precision/suppression path that goes all the way
to the CI gate.

## Remaining Gaps

- The modeled concrete semantics is narrow and conditional: "concrete CPG
  vulnerability" means "ordered sanitizer evidence is absent."
- Production use must prove that ordered/value-carrying sanitizer evidence is
  sound for the real language and framework.
- No path feasibility integration yet.
- No alias-sensitive value-token computation.
- No multi-sanitizer or parser-state chain.

## Next Theorem Candidate

Add a negative result/guardrail:

- a wrong-context sanitizer certificate must fail to suppress a finding whose
  sink requires another `SinkKind`;
- prove a CPG version of `wrong_context_sanitizer_does_not_prove_html_safe`.

That would make the CPG sanitizer triage theorem less optimistic and more useful
as a precision guard.

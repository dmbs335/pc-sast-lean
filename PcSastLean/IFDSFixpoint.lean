import PcSastLean.IFDS

/-!
IFDS fixpoint certificates.

`PcSastLean.IFDS` checks one path witness.  A real solver also needs a no-finding
certificate: a finite set of reachable exploded-supergraph nodes that contains
all seeds and is closed under graph edges.  If a target is outside that closed
set, no IFDS path can reach it.

This is deliberately an over-approximate certificate.  Closure under all edges is
stronger than closure under only valid call/return paths, so the resulting
no-reachability claim is sound.
-/

namespace PcSastLean

structure IFDSFixpointCert where
  reached : List IFDSNode
deriving Repr

def SeedsIncluded (seeds reached : List IFDSNode) : Prop :=
  forall seed, seed ∈ seeds -> seed ∈ reached

def EdgeClosed (graph : List IFDSEdge) (reached : List IFDSNode) : Prop :=
  forall edge, edge ∈ graph -> edge.src ∈ reached -> edge.dst ∈ reached

def IFDSFixpointCert.Valid
    (graph : List IFDSEdge) (seeds : List IFDSNode) (cert : IFDSFixpointCert) : Prop :=
  SeedsIncluded seeds cert.reached /\ EdgeClosed graph cert.reached

theorem ifds_path_in_closed_set
    {graph : List IFDSEdge} {reached : List IFDSNode}
    (hclosed : EdgeClosed graph reached) :
    forall {seed target actions},
      IFDSPath graph seed target actions ->
      seed ∈ reached ->
      target ∈ reached := by
  intro seed target actions hpath
  induction hpath with
  | refl n =>
      intro hseed
      exact hseed
  | cons hedge _ ih =>
      intro hseed
      exact ih (hclosed _ hedge hseed)

theorem ifds_reachable_in_fixpoint
    {graph : List IFDSEdge} {seeds : List IFDSNode} {cert : IFDSFixpointCert}
    (hvalid : cert.Valid graph seeds) :
    forall {target},
      IFDSReachable graph seeds target ->
      target ∈ cert.reached := by
  intro target hreach
  rcases hreach with ⟨seed, actions, hseed, hpath, _hvalidPath⟩
  exact ifds_path_in_closed_set hvalid.right hpath (hvalid.left seed hseed)

theorem ifds_no_reach_from_fixpoint
    {graph : List IFDSEdge} {seeds : List IFDSNode} {cert : IFDSFixpointCert}
    {target : IFDSNode}
    (hvalid : cert.Valid graph seeds)
    (hnot : target ∉ cert.reached) :
    ¬ IFDSReachable graph seeds target := by
  intro hreach
  exact hnot (ifds_reachable_in_fixpoint hvalid hreach)

/-! ## Decidable checker for finite fixpoint certificates -/

def checkSeedsIncluded (seeds reached : List IFDSNode) : Bool :=
  match seeds with
  | [] => true
  | seed :: rest => decide (seed ∈ reached) && checkSeedsIncluded rest reached

def checkEdgeClosed (graph : List IFDSEdge) (reached : List IFDSNode) : Bool :=
  match graph with
  | [] => true
  | edge :: rest =>
      decide (edge.src ∉ reached ∨ edge.dst ∈ reached) &&
      checkEdgeClosed rest reached

def checkIFDSFixpoint
    (graph : List IFDSEdge) (seeds : List IFDSNode) (cert : IFDSFixpointCert) : Bool :=
  checkSeedsIncluded seeds cert.reached &&
  checkEdgeClosed graph cert.reached

theorem checkSeedsIncluded_sound
    {seeds reached : List IFDSNode}
    (h : checkSeedsIncluded seeds reached = true) :
    SeedsIncluded seeds reached := by
  intro seed hseed
  induction seeds with
  | nil =>
      simp at hseed
  | cons head rest ih =>
      simp [checkSeedsIncluded] at h
      simp at hseed
      cases hseed with
      | inl heq =>
          subst heq
          exact h.left
      | inr hmem =>
          exact ih h.right hmem

theorem checkEdgeClosed_sound
    {graph : List IFDSEdge} {reached : List IFDSNode}
    (h : checkEdgeClosed graph reached = true) :
    EdgeClosed graph reached := by
  intro edge hedge hsrc
  induction graph with
  | nil =>
      simp at hedge
  | cons head rest ih =>
      simp [checkEdgeClosed] at h
      simp at hedge
      cases hedge with
      | inl heq =>
          subst heq
          cases h.left with
          | inl hnot =>
              exact False.elim (hnot hsrc)
          | inr hdst =>
              exact hdst
      | inr hmem =>
          exact ih h.right hmem

theorem checkIFDSFixpoint_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode} {cert : IFDSFixpointCert}
    (h : checkIFDSFixpoint graph seeds cert = true) :
    cert.Valid graph seeds := by
  simp [checkIFDSFixpoint, IFDSFixpointCert.Valid] at h
  exact And.intro (checkSeedsIncluded_sound h.left) (checkEdgeClosed_sound h.right)

theorem checked_ifds_no_reach
    {graph : List IFDSEdge} {seeds : List IFDSNode} {cert : IFDSFixpointCert}
    {target : IFDSNode}
    (hcheck : checkIFDSFixpoint graph seeds cert = true)
    (hnot : target ∉ cert.reached) :
    ¬ IFDSReachable graph seeds target := by
  exact ifds_no_reach_from_fixpoint (checkIFDSFixpoint_sound hcheck) hnot

/-! ## Demos -/

def ifdsFixpointCert : IFDSFixpointCert :=
  { reached := [ifdsSeed, ifdsCallNode, ifdsCalleeNode, ifdsReturnNode, ifdsSinkNode] }

example : checkIFDSFixpoint ifdsGraph [ifdsSeed] ifdsFixpointCert = true := by
  native_decide

def ifdsUnreachableNode : IFDSNode := { proc := 2, point := 0, fact := 99 }

example : ¬ IFDSReachable ifdsGraph [ifdsSeed] ifdsUnreachableNode :=
  checked_ifds_no_reach
    (cert := ifdsFixpointCert)
    (by native_decide)
    (by simp [ifdsFixpointCert, ifdsUnreachableNode, ifdsSeed, ifdsCallNode,
      ifdsCalleeNode, ifdsReturnNode, ifdsSinkNode])

end PcSastLean

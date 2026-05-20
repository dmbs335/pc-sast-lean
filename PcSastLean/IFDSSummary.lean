import PcSastLean.IFDSFixpoint

/-!
IFDS summary-edge certificates.

Real IFDS/tabulation solvers do not always emit a raw edge-by-edge path.  They
often reuse summary edges that stand for an already-checked intraprocedural or
callee path.  This module adds a certificate layer for that solver artifact:
summary segments may be used in a compressed finding certificate only when Lean
can expand them back to ordinary IFDS paths over the original exploded
supergraph.

Claim boundary:

* Verified here: checked compressed IFDS paths expand to ordinary IFDS paths and
  preserve valid call/return action discipline.
* External obligations: the solver implementation is untrusted and must emit
  checkable segments.
* Not modeled here: tabulation algorithm correctness, performance, or precision.
-/

namespace PcSastLean

structure IFDSSummaryCert where
  src : IFDSNode
  dst : IFDSNode
  hops : List IFDSHop
deriving Repr

def IFDSSummaryCert.actions (cert : IFDSSummaryCert) : List Action :=
  hopActions cert.hops

def checkIFDSSummary (graph : List IFDSEdge) (cert : IFDSSummaryCert) : Bool :=
  checkHops graph cert.hops cert.src cert.dst &&
  checkValidActions cert.actions

def IFDSSummaryCert.Sound (graph : List IFDSEdge) (cert : IFDSSummaryCert) : Prop :=
  IFDSPath graph cert.src cert.dst cert.actions /\ ValidActions cert.actions

theorem checkIFDSSummary_sound
    {graph : List IFDSEdge} {cert : IFDSSummaryCert}
    (h : checkIFDSSummary graph cert = true) :
    cert.Sound graph := by
  simp [checkIFDSSummary, IFDSSummaryCert.Sound, IFDSSummaryCert.actions] at h
  exact And.intro
    (hopsPath_to_IFDSPath cert.hops cert.src cert.dst
      (checkHops_sound cert.hops cert.src cert.dst h.left))
    (checkValidActions_sound h.right)

def SummariesSound (graph : List IFDSEdge) (summaries : List IFDSSummaryCert) : Prop :=
  forall cert, cert ∈ summaries -> cert.Sound graph

def checkIFDSSummaries (graph : List IFDSEdge) : List IFDSSummaryCert -> Bool
  | [] => true
  | cert :: rest => checkIFDSSummary graph cert && checkIFDSSummaries graph rest

theorem checkIFDSSummaries_sound
    {graph : List IFDSEdge} {summaries : List IFDSSummaryCert}
    (h : checkIFDSSummaries graph summaries = true) :
    SummariesSound graph summaries := by
  intro cert hmem
  induction summaries with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      simp [checkIFDSSummaries] at h
      simp at hmem
      cases hmem with
      | inl heq =>
          subst heq
          exact checkIFDSSummary_sound h.left
      | inr htail =>
          exact ih h.right htail

inductive IFDSSegment where
  | hop (hop : IFDSHop)
  | summary (cert : IFDSSummaryCert)
deriving Repr

def segmentSrc : IFDSSegment -> IFDSNode
  | IFDSSegment.hop hop => hop.src
  | IFDSSegment.summary cert => cert.src

def segmentDst : IFDSSegment -> IFDSNode
  | IFDSSegment.hop hop => hop.dst
  | IFDSSegment.summary cert => cert.dst

def segmentActions : IFDSSegment -> List Action
  | IFDSSegment.hop hop => [hop.action]
  | IFDSSegment.summary cert => cert.actions

def checkIFDSSegment (graph : List IFDSEdge) : IFDSSegment -> Bool
  | IFDSSegment.hop hop => decide (hopEdge hop ∈ graph)
  | IFDSSegment.summary cert => checkIFDSSummary graph cert

def compressedActions : List IFDSSegment -> List Action
  | [] => []
  | seg :: rest => segmentActions seg ++ compressedActions rest

def checkCompressedSegments
    (graph : List IFDSEdge) : List IFDSSegment -> IFDSNode -> IFDSNode -> Bool
  | [], seed, target => decide (seed = target)
  | seg :: rest, seed, target =>
      decide (segmentSrc seg = seed) &&
      checkIFDSSegment graph seg &&
      checkCompressedSegments graph rest (segmentDst seg) target

theorem ifds_path_append
    {graph : List IFDSEdge} :
    forall {a b c acts₁ acts₂},
      IFDSPath graph a b acts₁ ->
      IFDSPath graph b c acts₂ ->
      IFDSPath graph a c (acts₁ ++ acts₂) := by
  intro a b c acts₁ acts₂ hleft hright
  induction hleft with
  | refl n =>
      simp
      exact hright
  | cons hedge _ ih =>
      simp
      exact IFDSPath.cons hedge (ih hright)

theorem checked_segment_to_path
    {graph : List IFDSEdge} {seg : IFDSSegment}
    (h : checkIFDSSegment graph seg = true) :
    IFDSPath graph (segmentSrc seg) (segmentDst seg) (segmentActions seg) := by
  cases seg with
  | hop hop =>
      simp [checkIFDSSegment, segmentSrc, segmentDst, segmentActions] at h ⊢
      exact IFDSPath.cons h (IFDSPath.refl hop.dst)
  | summary cert =>
      simpa [segmentSrc, segmentDst, segmentActions] using (checkIFDSSummary_sound h).left

theorem checked_compressed_segments_to_path
    {graph : List IFDSEdge} :
    forall segments seed target,
      checkCompressedSegments graph segments seed target = true ->
      IFDSPath graph seed target (compressedActions segments) := by
  intro segments
  induction segments with
  | nil =>
      intro seed target h
      simp [checkCompressedSegments] at h
      subst h
      exact IFDSPath.refl seed
  | cons seg rest ih =>
      intro seed target h
      simp [checkCompressedSegments] at h
      have hsrc : segmentSrc seg = seed := h.left.left
      have hseg : checkIFDSSegment graph seg = true := h.left.right
      have hrest : checkCompressedSegments graph rest (segmentDst seg) target = true := h.right
      subst hsrc
      simp [compressedActions]
      exact ifds_path_append (checked_segment_to_path hseg) (ih (segmentDst seg) target hrest)

structure IFDSCompressedCert where
  seed : IFDSNode
  target : IFDSNode
  segments : List IFDSSegment
deriving Repr

def checkIFDSCompressedCert
    (graph : List IFDSEdge) (seeds : List IFDSNode)
    (cert : IFDSCompressedCert) : Bool :=
  decide (cert.seed ∈ seeds) &&
  checkCompressedSegments graph cert.segments cert.seed cert.target &&
  checkValidActions (compressedActions cert.segments)

theorem checked_ifds_compressed_cert_sound
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCompressedCert}
    (h : checkIFDSCompressedCert graph seeds cert = true) :
    IFDSReachable graph seeds cert.target := by
  simp [checkIFDSCompressedCert] at h
  exact ⟨cert.seed, compressedActions cert.segments, h.left.left,
    checked_compressed_segments_to_path cert.segments cert.seed cert.target h.left.right,
    checkValidActions_sound h.right⟩

/-! ## Demo -/

def ifdsCallSummary : IFDSSummaryCert :=
  { src := ifdsCallNode
  , dst := ifdsReturnNode
  , hops :=
      [ { src := ifdsCallNode, dst := ifdsCalleeNode, action := Action.call 7 }
      , { src := ifdsCalleeNode, dst := ifdsReturnNode, action := Action.ret 7 }
      ]
  }

example : checkIFDSSummary ifdsGraph ifdsCallSummary = true := by
  native_decide

def ifdsCompressedCert : IFDSCompressedCert :=
  { seed := ifdsSeed
  , target := ifdsSinkNode
  , segments :=
      [ IFDSSegment.hop { src := ifdsSeed, dst := ifdsCallNode, action := Action.normal }
      , IFDSSegment.summary ifdsCallSummary
      , IFDSSegment.hop { src := ifdsReturnNode, dst := ifdsSinkNode, action := Action.normal }
      ]
  }

example :
    checkIFDSCompressedCert ifdsGraph [ifdsSeed] ifdsCompressedCert = true := by
  native_decide

example : IFDSReachable ifdsGraph [ifdsSeed] ifdsSinkNode :=
  checked_ifds_compressed_cert_sound
    (cert := ifdsCompressedCert)
    (by native_decide)

end PcSastLean

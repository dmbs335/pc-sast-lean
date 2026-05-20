import PcSastLean.CPG

/-!
IFDS-to-CPG embedding.

IFDS and CPG are not equivalent theories.  IFDS is a disciplined
interprocedural data-flow reachability problem over an exploded supergraph,
while CPG is a broader typed program graph.  This module proves one precise
integration fact: an accepted IFDS path certificate can be embedded as an
accepted CPG-style path certificate over the encoded IFDS graph.

Claim boundary:

* Verified here: IFDS path certificates embed into a CPG-style path certificate
  language over an encoded exploded supergraph.
* External obligations: a production CPG still needs its own extraction
  provenance and source-level mapping.
* Not modeled here: equivalence between IFDS and full CPG expressiveness.
-/

namespace PcSastLean

def ifdsNodeId (n : IFDSNode) : CPGId :=
  n.proc * 1000000 + n.point * 1000 + n.fact

def ifdsActionKind : Action -> CPGEdgeKind
  | Action.normal => CPGEdgeKind.data
  | Action.call _ => CPGEdgeKind.call
  | Action.ret _ => CPGEdgeKind.ret

def ifdsNodeToCPGNode (loc : SourceLoc) (n : IFDSNode) : CPGNode :=
  { id := ifdsNodeId n, kind := CPGNodeKind.stmt, loc := loc }

def ifdsEdgeToCPGEdge (loc : SourceLoc) (e : IFDSEdge) : CPGEdge :=
  { src := ifdsNodeId e.src
  , dst := ifdsNodeId e.dst
  , kind := ifdsActionKind e.action
  , loc := loc
  }

def ifdsGraphToCPGEdges (loc : SourceLoc) (graph : List IFDSEdge) : List CPGEdge :=
  graph.map (ifdsEdgeToCPGEdge loc)

def ifdsGraphToCPGNodes (loc : SourceLoc) : List IFDSEdge -> List CPGNode
  | [] => []
  | e :: rest =>
      ifdsNodeToCPGNode loc e.src ::
      ifdsNodeToCPGNode loc e.dst ::
      ifdsGraphToCPGNodes loc rest

def ifdsCPGNodes
    (loc : SourceLoc) (graph : List IFDSEdge) (cert : IFDSCheckedCert) :
    List CPGNode :=
  ifdsNodeToCPGNode loc cert.seed ::
  ifdsNodeToCPGNode loc cert.target ::
  ifdsGraphToCPGNodes loc graph

def ifdsHopToCPGHop (loc : SourceLoc) (h : IFDSHop) : CPGHop :=
  { src := ifdsNodeId h.src
  , dst := ifdsNodeId h.dst
  , kind := ifdsActionKind h.action
  , loc := loc
  }

def ifdsHopsToCPGHops (loc : SourceLoc) : List IFDSHop -> List CPGHop
  | [] => []
  | h :: rest => ifdsHopToCPGHop loc h :: ifdsHopsToCPGHops loc rest

def ifdsCertToCPGCert (loc : SourceLoc) (cert : IFDSCheckedCert) : CPGFindingCert :=
  { source := ifdsNodeId cert.seed
  , sink := ifdsNodeId cert.target
  , hops := ifdsHopsToCPGHops loc cert.hops
  }

theorem checkCPGHops_of_checkHops
    {graph : List IFDSEdge} {loc : SourceLoc} :
    forall hops seed target,
      checkHops graph hops seed target = true ->
      checkCPGHops (ifdsGraphToCPGEdges loc graph)
        (ifdsHopsToCPGHops loc hops)
        (ifdsNodeId seed)
        (ifdsNodeId target) = true := by
  intro hops
  induction hops with
  | nil =>
      intro seed target h
      simp [checkHops] at h
      subst h
      simp [checkCPGHops, ifdsHopsToCPGHops]
  | cons hop rest ih =>
      intro seed target h
      simp [checkHops] at h
      have hsrc : hop.src = seed := h.left.left
      have hedgeIFDS : hopEdge hop ∈ graph := h.left.right
      have hrest : checkHops graph rest hop.dst target = true := h.right
      have hedgeCPG :
          (ifdsHopToCPGHop loc hop).edge ∈ ifdsGraphToCPGEdges loc graph := by
        exact List.mem_map.mpr
          ⟨hopEdge hop, hedgeIFDS, by
            simp [ifdsHopToCPGHop, ifdsEdgeToCPGEdge, hopEdge, CPGHop.edge]⟩
      subst hsrc
      simp [checkCPGHops, ifdsHopsToCPGHops, ifdsHopToCPGHop]
      exact And.intro hedgeCPG (ih hop.dst target hrest)

theorem ifds_cert_embeds_as_cpg_cert
    {graph : List IFDSEdge} {seeds : List IFDSNode}
    {cert : IFDSCheckedCert} {loc : SourceLoc}
    (hcert : checkIFDSCert graph seeds cert = true) :
    checkCPGFinding
      (ifdsCPGNodes loc graph cert)
      (ifdsGraphToCPGEdges loc graph)
      [ifdsNodeId cert.seed]
      [ifdsNodeId cert.target]
      (ifdsCertToCPGCert loc cert) = true := by
  simp [checkIFDSCert] at hcert
  have hhops := checkCPGHops_of_checkHops
    (loc := loc) cert.hops cert.seed cert.target hcert.left.right
  simp [checkCPGFinding, ifdsCertToCPGCert, ifdsCPGNodes, checkHasNode,
    nodeIds, ifdsNodeToCPGNode, hhops]

/-! ## Demo -/

def ifdsAsCPGCert : CPGFindingCert :=
  ifdsCertToCPGCert demoLoc ifdsCert

example :
    checkCPGFinding
      (ifdsCPGNodes demoLoc ifdsGraph ifdsCert)
      (ifdsGraphToCPGEdges demoLoc ifdsGraph)
      [ifdsNodeId ifdsCert.seed]
      [ifdsNodeId ifdsCert.target]
      ifdsAsCPGCert = true :=
  ifds_cert_embeds_as_cpg_cert (seeds := [ifdsSeed]) (by native_decide)

example :
    CPGFinding
      (ifdsGraphToCPGEdges demoLoc ifdsGraph)
      [ifdsNodeId ifdsCert.seed]
      [ifdsNodeId ifdsCert.target]
      ifdsAsCPGCert.source
      ifdsAsCPGCert.sink :=
  checked_cpg_finding_sound
    (nodes := ifdsCPGNodes demoLoc ifdsGraph ifdsCert)
    (cert := ifdsAsCPGCert)
    (ifds_cert_embeds_as_cpg_cert (seeds := [ifdsSeed]) (by native_decide))

end PcSastLean

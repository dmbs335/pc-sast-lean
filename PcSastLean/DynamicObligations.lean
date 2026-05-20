import PcSastLean.FixGate

/-!
Dynamic obligations.

Dynamic features are exactly where an unconditional SAST theorem becomes false:
reflection, framework routing, eval-like calls, plugins, generated code, and
configuration-driven dispatch may create behavior that the static graph did not
see.

This module models a useful engineering response.  A dynamic call is sound only
when it is discharged by an obligation: a framework model, runtime trace
coverage, allowlist, generated-code extractor, or another trusted witness.  Once
all dynamic blocks are discharged, the same fix-gate style conclusion becomes
available again.

Claim boundary:

* Verified here: dynamic blocks compose with fix/baseline gates after each block
  supplies a sound summary witness.
* External obligations: the witness must be justified by a framework model,
  generated-code extractor, runtime coverage argument, or another trusted source.
* Not modeled here: the operational semantics of reflection, eval, plugin
  loading, async callbacks, or framework internals.
-/

namespace PcSastLean

structure DynamicWitness where
  summary : Summary

structure DynamicBlock where
  body : List Instr
  witness : DynamicWitness

def DynamicBlockSound (b : DynamicBlock) : Prop :=
  SummarySound b.body b.witness.summary

inductive DBlock where
  | staticBlock (b : Block) : DBlock
  | dynamicCall (b : DynamicBlock) : DBlock

def DBlockSound : DBlock -> Prop
  | DBlock.staticBlock b => BlockSound b
  | DBlock.dynamicCall b => DynamicBlockSound b

def execConcreteDBlock (s : Store) : DBlock -> Store × List Node
  | DBlock.staticBlock b => execConcreteBlock s b
  | DBlock.dynamicCall b => exec s b.body

def execAbstractDBlock (s : Store) : DBlock -> Store × List Node
  | DBlock.staticBlock b => execAbstractBlock s b
  | DBlock.dynamicCall b => b.witness.summary s

def execConcreteDBlocks (s : Store) : List DBlock -> Store × List Node
  | [] => (s, [])
  | b :: rest =>
      let r := execConcreteDBlock s b
      let next := execConcreteDBlocks r.1 rest
      (next.1, r.2 ++ next.2)

def execAbstractDBlocks (s : Store) : List DBlock -> Store × List Node
  | [] => (s, [])
  | b :: rest =>
      let r := execAbstractDBlock s b
      let next := execAbstractDBlocks r.1 rest
      (next.1, r.2 ++ next.2)

theorem dblock_sound
    {concrete abstract : Store} {b : DBlock}
    (hb : DBlockSound b)
    (hs : Store.le concrete abstract) :
    Store.le (execConcreteDBlock concrete b).1 (execAbstractDBlock abstract b).1 /\
    ListSubset (execConcreteDBlock concrete b).2 (execAbstractDBlock abstract b).2 := by
  cases b with
  | staticBlock sb =>
      exact block_sound hb hs
  | dynamicCall db =>
      exact hb concrete abstract hs

theorem dblocks_sound
    {concrete abstract : Store} :
    forall blocks : List DBlock,
      (forall b, b ∈ blocks -> DBlockSound b) ->
      Store.le concrete abstract ->
      Store.le (execConcreteDBlocks concrete blocks).1 (execAbstractDBlocks abstract blocks).1 /\
      ListSubset (execConcreteDBlocks concrete blocks).2 (execAbstractDBlocks abstract blocks).2 := by
  intro blocks
  induction blocks generalizing concrete abstract with
  | nil =>
      intro _ hs
      constructor
      · exact hs
      · intro id hmem
        simp [execConcreteDBlocks] at hmem
  | cons b rest ih =>
      intro hall hs
      have hb : DBlockSound b := hall b (by simp)
      have hfirst := dblock_sound hb hs
      have hrestAll : forall rb, rb ∈ rest -> DBlockSound rb := by
        intro rb hr
        exact hall rb (by simp [hr])
      have htail := ih hrestAll hfirst.left
      constructor
      · simp [execConcreteDBlocks, execAbstractDBlocks]
        exact htail.left
      · intro id hmem
        simp [execConcreteDBlocks, execAbstractDBlocks] at hmem ⊢
        cases hmem with
        | inl hhead =>
            exact Or.inl (hfirst.right id hhead)
        | inr hrest =>
            exact Or.inr (htail.right id hrest)

theorem dynamic_fix_gate
    {concrete abstract : Store} {patched : List DBlock} {sink : Node}
    (hall : forall b, b ∈ patched -> DBlockSound b)
    (hs : Store.le concrete abstract)
    (habs : SinkRemoved sink (execAbstractDBlocks abstract patched).2) :
    SinkRemoved sink (execConcreteDBlocks concrete patched).2 := by
  intro hbad
  exact habs ((dblocks_sound patched hall hs).right sink hbad)

theorem dynamic_baseline_gate
    {concrete abstract : Store} {blocks : List DBlock} {baseline : List Node}
    (hall : forall b, b ∈ blocks -> DBlockSound b)
    (hs : Store.le concrete abstract)
    (habs : CoveredByBaseline (execAbstractDBlocks abstract blocks).2 baseline) :
    NoNewConcreteViolations (execConcreteDBlocks concrete blocks).2 baseline := by
  exact ListSubset.trans (dblocks_sound blocks hall hs).right habs

/-! ## Demos -/

def dynamicVulnerableBody : List Instr :=
  [ Instr.source 4
  , Instr.sink 4 23
  ]

def dynamicSanitizedBody : List Instr :=
  [ Instr.source 4
  , Instr.sanitize 5 4
  , Instr.sink 5 23
  ]

def dynamicSanitizedWitness : DynamicWitness :=
  { summary := exactSummary dynamicSanitizedBody }

def dynamicPatchedBlocks : List DBlock :=
  [ DBlock.dynamicCall
      { body := dynamicSanitizedBody
      , witness := dynamicSanitizedWitness
      }
  ]

theorem dynamicPatchedBlocksSound :
    forall b, b ∈ dynamicPatchedBlocks -> DBlockSound b := by
  intro b hb
  simp [dynamicPatchedBlocks] at hb
  subst hb
  exact exactSummary_sound dynamicSanitizedBody

example : SinkRemoved 23 (execAbstractDBlocks emptyStore dynamicPatchedBlocks).2 := by
  unfold SinkRemoved
  native_decide

example : SinkRemoved 23 (execConcreteDBlocks emptyStore dynamicPatchedBlocks).2 :=
  dynamic_fix_gate
    dynamicPatchedBlocksSound
    (Store.le_refl emptyStore)
    (by
      unfold SinkRemoved
      native_decide)

end PcSastLean

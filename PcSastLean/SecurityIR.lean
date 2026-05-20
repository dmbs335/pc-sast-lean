import PcSastLean.Basic

/-!
An executable miniature Security IR.

This module connects three strands of SAST theory:

* abstract interpretation: stores are ordered by precision;
* taint analysis: source, propagation, sanitizer, and sink instructions;
* proof-carrying SAST: accepted certificates imply trusted policy facts.

Claim boundary:

* Verified here: soundness of this tiny IR's taint transfer functions, branches,
  procedure summaries, and safety/finding gates.
* External obligations: any real source language must be extracted into this IR
  with a separate soundness certificate.
* Not modeled here: pointer arithmetic, async/callback scheduling, exception
  flow, reflection, native APIs, or production build semantics.
-/

namespace PcSastLean

inductive Label where
  | clean : Label
  | tainted : Label
deriving DecidableEq, Repr

namespace Label

def le : Label -> Label -> Prop
  | clean, _ => True
  | tainted, tainted => True
  | tainted, clean => False

def join : Label -> Label -> Label
  | tainted, _ => tainted
  | _, tainted => tainted
  | clean, clean => clean

theorem le_refl (x : Label) : le x x := by
  cases x <;> trivial

theorem le_trans {x y z : Label} (hxy : le x y) (hyz : le y z) : le x z := by
  cases x <;> cases y <;> cases z <;> trivial

end Label

abbrev Store := Var -> Label

def Store.le (c a : Store) : Prop :=
  forall v, Label.le (c v) (a v)

def Store.set (s : Store) (x : Var) (l : Label) : Store :=
  fun v => if v = x then l else s v

theorem Store.set_le
    {c a : Store} {x : Var} {lc la : Label}
    (hs : Store.le c a) (hl : Label.le lc la) :
    Store.le (Store.set c x lc) (Store.set a x la) := by
  intro v
  unfold Store.set
  by_cases h : v = x
  · simp [h, hl]
  · simp [h, hs v]

theorem Store.le_refl (s : Store) : Store.le s s := by
  intro v
  exact Label.le_refl (s v)

def Store.join (l r : Store) : Store :=
  fun v => Label.join (l v) (r v)

theorem Label.le_join_left (x y : Label) : Label.le x (Label.join x y) := by
  cases x <;> cases y <;> trivial

theorem Label.le_join_right (x y : Label) : Label.le y (Label.join x y) := by
  cases x <;> cases y <;> trivial

theorem Store.le_join_left (l r : Store) : Store.le l (Store.join l r) := by
  intro v
  exact Label.le_join_left (l v) (r v)

theorem Store.le_join_right (l r : Store) : Store.le r (Store.join l r) := by
  intro v
  exact Label.le_join_right (l v) (r v)

theorem Store.le_join
    {c a b : Store}
    (ha : Store.le c a) :
    Store.le c (Store.join a b) := by
  intro v
  exact Label.le_trans (ha v) (Label.le_join_left (a v) (b v))

theorem Store.le_join_of_right
    {c a b : Store}
    (hb : Store.le c b) :
    Store.le c (Store.join a b) := by
  intro v
  exact Label.le_trans (hb v) (Label.le_join_right (a v) (b v))

inductive Instr where
  | source (dst : Var)
  | assign (dst src : Var)
  | sanitize (dst src : Var)
  | sink (src : Var) (id : Node)
deriving DecidableEq, Repr

structure StepResult where
  store : Store
  violation : Option Node

def step (s : Store) : Instr -> StepResult
  | Instr.source dst =>
      { store := Store.set s dst Label.tainted, violation := none }
  | Instr.assign dst src =>
      { store := Store.set s dst (s src), violation := none }
  | Instr.sanitize dst _src =>
      { store := Store.set s dst Label.clean, violation := none }
  | Instr.sink src id =>
      { store := s, violation := if s src = Label.tainted then some id else none }

def exec (s : Store) : List Instr -> Store × List Node
  | [] => (s, [])
  | i :: rest =>
      let r := step s i
      let next := exec r.store rest
      match r.violation with
      | none => next
      | some id => (next.1, id :: next.2)

theorem step_store_sound
    {c a : Store} {i : Instr}
    (hs : Store.le c a) :
    Store.le (step c i).store (step a i).store := by
  cases i with
  | source dst =>
      exact Store.set_le hs (Label.le_refl Label.tainted)
  | assign dst src =>
      exact Store.set_le hs (hs src)
  | sanitize dst src =>
      exact Store.set_le hs (Label.le_refl Label.clean)
  | sink src id =>
      exact hs

def hasViolation (id : Node) (r : Store × List Node) : Prop :=
  id ∈ r.2

theorem exec_store_sound
    {c a : Store} :
    forall prog : List Instr,
      Store.le c a ->
      Store.le (exec c prog).1 (exec a prog).1 := by
  intro prog
  induction prog generalizing c a with
  | nil =>
      intro hs
      exact hs
  | cons i rest ih =>
      intro hs
      simp [exec]
      cases (step c i).violation <;> cases (step a i).violation <;>
        simp <;>
        exact ih (step_store_sound (i := i) hs)

def ListSubset (xs ys : List Node) : Prop :=
  forall id, id ∈ xs -> id ∈ ys

theorem ListSubset.append_left {xs ys : List Node} :
    ListSubset xs (xs ++ ys) := by
  intro id h
  exact List.mem_append_left ys h

theorem ListSubset.append_right {xs ys : List Node} :
    ListSubset ys (xs ++ ys) := by
  intro id h
  exact List.mem_append_right xs h

theorem ListSubset.trans {xs ys zs : List Node}
    (hxy : ListSubset xs ys) (hyz : ListSubset ys zs) :
    ListSubset xs zs := by
  intro id h
  exact hyz id (hxy id h)

def StepResult.violations (r : StepResult) : List Node :=
  match r.violation with
  | none => []
  | some id => [id]

theorem step_violation_sound
    {c a : Store} {i : Instr}
    (hs : Store.le c a) :
    ListSubset (step c i).violations (step a i).violations := by
  intro id hmem
  cases i with
  | source dst =>
      simp [step, StepResult.violations] at hmem
  | assign dst src =>
      simp [step, StepResult.violations] at hmem
  | sanitize dst src =>
      simp [step, StepResult.violations] at hmem
  | sink src sinkId =>
      have hle := hs src
      cases hc : c src <;> cases ha : a src
      · simp [step, StepResult.violations, hc, ha] at hmem
      · simp [step, StepResult.violations, hc, ha] at hmem
      · simp [Label.le, hc, ha] at hle
      · simp [step, StepResult.violations, hc, ha] at hmem ⊢
        exact hmem

theorem exec_sound
    {c a : Store} :
    forall prog : List Instr,
      Store.le c a ->
      Store.le (exec c prog).1 (exec a prog).1 /\
      ListSubset (exec c prog).2 (exec a prog).2 := by
  intro prog
  induction prog generalizing c a with
  | nil =>
      intro hs
      constructor
      · exact hs
      · intro id hmem
        simp [exec] at hmem
  | cons i rest ih =>
      intro hs
      constructor
      · exact exec_store_sound (i :: rest) hs
      · intro id hmem
        have htail := (ih (step_store_sound (i := i) hs)).right
        have hhead := step_violation_sound (i := i) hs
        cases hc : (step c i).violation with
        | none =>
            cases ha : (step a i).violation with
            | none =>
                simp [exec, hc, ha] at hmem ⊢
                exact htail id hmem
            | some aid =>
                simp [exec, hc, ha] at hmem ⊢
                exact Or.inr (htail id hmem)
        | some cid =>
            cases ha : (step a i).violation with
            | none =>
                simp [exec, hc, ha] at hmem ⊢
                cases hmem with
                | inl hid =>
                    subst hid
                    have hsingle : id ∈ (step c i).violations := by
                      simp [StepResult.violations, hc]
                    have habs := hhead id hsingle
                    simp [StepResult.violations, ha] at habs
                | inr hrest =>
                    exact htail id hrest
            | some aid =>
                simp [exec, hc, ha] at hmem ⊢
                cases hmem with
                | inl hid =>
                    subst hid
                    have hsingle : id ∈ (step c i).violations := by
                      simp [StepResult.violations, hc]
                    have habs := hhead id hsingle
                    simp [StepResult.violations, ha] at habs
                    exact Or.inl habs
                | inr hrest =>
                    exact Or.inr (htail id hrest)

/-! ## Certificates over the executable IR -/

def instrMentionsSink (id : Node) : Instr -> Bool
  | Instr.sink _ sinkId => decide (sinkId = id)
  | _ => false

def programMentionsSink (prog : List Instr) (id : Node) : Bool :=
  match prog with
  | [] => false
  | i :: rest => instrMentionsSink id i || programMentionsSink rest id

structure SinkCert where
  sinkId : Node
deriving Repr

def checkSinkCert (prog : List Instr) (c : SinkCert) : Bool :=
  programMentionsSink prog c.sinkId

def SinkInProgram (prog : List Instr) (id : Node) : Prop :=
  exists src : Var, Instr.sink src id ∈ prog

theorem instrMentionsSink_sound
    {id : Node} {i : Instr}
    (h : instrMentionsSink id i = true) :
    exists src : Var, i = Instr.sink src id := by
  cases i with
  | source dst =>
      simp [instrMentionsSink] at h
  | assign dst src =>
      simp [instrMentionsSink] at h
  | sanitize dst src =>
      simp [instrMentionsSink] at h
  | sink src sinkId =>
      simp [instrMentionsSink] at h
      exact Exists.intro src (by simp [h])

theorem programMentionsSink_sound
    {prog : List Instr} {id : Node}
    (h : programMentionsSink prog id = true) :
    SinkInProgram prog id := by
  induction prog with
  | nil =>
      simp [programMentionsSink] at h
  | cons i rest ih =>
      simp [programMentionsSink] at h
      cases h with
      | inl hi =>
          rcases instrMentionsSink_sound hi with ⟨src, rfl⟩
          exact Exists.intro src (by simp)
      | inr hr =>
          rcases ih hr with ⟨src, hmem⟩
          exact Exists.intro src (by simp [hmem])

theorem accepted_sink_cert_sound
    {prog : List Instr} {c : SinkCert}
    (h : checkSinkCert prog c = true) :
    SinkInProgram prog c.sinkId := by
  exact programMentionsSink_sound h

/-! ## Concrete finding and safety certificates -/

def ConcreteViolation (s : Store) (prog : List Instr) (id : Node) : Prop :=
  id ∈ (exec s prog).2

def SafeProgram (s : Store) (prog : List Instr) : Prop :=
  forall id : Node, id ∉ (exec s prog).2

def checkConcreteFinding (s : Store) (prog : List Instr) (c : SinkCert) : Bool :=
  decide (c.sinkId ∈ (exec s prog).2)

def checkConcreteSafety (s : Store) (prog : List Instr) : Bool :=
  decide ((exec s prog).2 = [])

theorem accepted_concrete_finding_sound
    {s : Store} {prog : List Instr} {c : SinkCert}
    (h : checkConcreteFinding s prog c = true) :
    ConcreteViolation s prog c.sinkId := by
  unfold checkConcreteFinding at h
  unfold ConcreteViolation
  exact of_decide_eq_true h

theorem accepted_concrete_safety_sound
    {s : Store} {prog : List Instr}
    (h : checkConcreteSafety s prog = true) :
    SafeProgram s prog := by
  unfold checkConcreteSafety at h
  have hempty : (exec s prog).2 = [] := of_decide_eq_true h
  intro id hid
  simp [hempty] at hid

theorem abstract_safety_implies_concrete_safety
    {concrete abstract : Store} {prog : List Instr}
    (hs : Store.le concrete abstract)
    (ha : SafeProgram abstract prog) :
    SafeProgram concrete prog := by
  intro id hbad
  have hsubset := (exec_sound prog hs).right
  exact ha id (hsubset id hbad)

theorem accepted_abstract_safety_gate_sound
    {concrete abstract : Store} {prog : List Instr}
    (hs : Store.le concrete abstract)
    (hcheck : checkConcreteSafety abstract prog = true) :
    SafeProgram concrete prog := by
  exact abstract_safety_implies_concrete_safety hs
    (accepted_concrete_safety_sound hcheck)

/-! ## Branch/join layer -/

def execConcreteBranch
    (chooseThen : Bool) (s : Store)
    (thenProg elseProg : List Instr) : Store × List Node :=
  if chooseThen then exec s thenProg else exec s elseProg

def execAbstractBranch
    (s : Store)
    (thenProg elseProg : List Instr) : Store × List Node :=
  let thenResult := exec s thenProg
  let elseResult := exec s elseProg
  (Store.join thenResult.1 elseResult.1, thenResult.2 ++ elseResult.2)

theorem branch_sound
    {concrete abstract : Store}
    {thenProg elseProg : List Instr}
    (chooseThen : Bool)
    (hs : Store.le concrete abstract) :
    Store.le
      (execConcreteBranch chooseThen concrete thenProg elseProg).1
      (execAbstractBranch abstract thenProg elseProg).1 /\
    ListSubset
      (execConcreteBranch chooseThen concrete thenProg elseProg).2
      (execAbstractBranch abstract thenProg elseProg).2 := by
  cases chooseThen
  · constructor
    · unfold execConcreteBranch execAbstractBranch
      simp
      exact Store.le_join_of_right (exec_store_sound elseProg hs)
    · unfold execConcreteBranch execAbstractBranch
      simp
      exact ListSubset.trans (exec_sound elseProg hs).right ListSubset.append_right
  · constructor
    · unfold execConcreteBranch execAbstractBranch
      simp
      exact Store.le_join (exec_store_sound thenProg hs)
    · unfold execConcreteBranch execAbstractBranch
      simp
      exact ListSubset.trans (exec_sound thenProg hs).right ListSubset.append_left

theorem branch_abstract_safety_implies_concrete_safety
    {concrete abstract : Store}
    {thenProg elseProg : List Instr}
    (chooseThen : Bool)
    (hs : Store.le concrete abstract)
    (habs : forall id : Node,
      id ∉ (execAbstractBranch abstract thenProg elseProg).2) :
    forall id : Node,
      id ∉ (execConcreteBranch chooseThen concrete thenProg elseProg).2 := by
  intro id hbad
  exact habs id ((branch_sound chooseThen hs).right id hbad)

/-! ## Procedure summaries and calls -/

def Summary := Store -> Store × List Node

def SummarySound (body : List Instr) (summary : Summary) : Prop :=
  forall concrete abstract : Store,
    Store.le concrete abstract ->
    Store.le (exec concrete body).1 (summary abstract).1 /\
    ListSubset (exec concrete body).2 (summary abstract).2

def exactSummary (body : List Instr) : Summary :=
  fun s => exec s body

theorem exactSummary_sound (body : List Instr) :
    SummarySound body (exactSummary body) := by
  intro concrete abstract hs
  exact exec_sound body hs

def cleanStore : Store :=
  fun _ => Label.clean

namespace Labels

def le : List Label -> List Label -> Prop
  | [], [] => True
  | c :: cs, a :: as => Label.le c a /\ le cs as
  | _, _ => False

theorem le_refl : forall xs : List Label, le xs xs := by
  intro xs
  induction xs with
  | nil =>
      trivial
  | cons x rest ih =>
      exact And.intro (Label.le_refl x) ih

end Labels

def argLabels (s : Store) (args : List Var) : List Label :=
  args.map s

theorem argLabels_sound
    {concrete abstract : Store} {args : List Var}
    (hs : Store.le concrete abstract) :
    Labels.le (argLabels concrete args) (argLabels abstract args) := by
  induction args with
  | nil =>
      simp [argLabels, Labels.le]
  | cons arg rest ih =>
      unfold argLabels
      simp [Labels.le]
      exact And.intro (hs arg) (by simpa [argLabels] using ih)

def bindLabels (base : Store) : List Var -> List Label -> Store
  | [], _ => base
  | _, [] => base
  | p :: params, l :: labels =>
      bindLabels (Store.set base p l) params labels

structure Proc where
  params : List Var
  ret : Var
  body : List Instr
deriving Repr

def execProcBody (proc : Proc) (args : List Label) : Store × List Node :=
  exec (bindLabels cleanStore proc.params args) proc.body

def ProcSummary := List Label -> Label × List Node

def ProcSummarySound (proc : Proc) (summary : ProcSummary) : Prop :=
  forall concreteArgs abstractArgs : List Label,
    Labels.le concreteArgs abstractArgs ->
    Label.le ((execProcBody proc concreteArgs).1 proc.ret) (summary abstractArgs).1 /\
    ListSubset (execProcBody proc concreteArgs).2 (summary abstractArgs).2

def execConcreteProcCall
    (s : Store) (proc : Proc) (args : List Var) (dst : Var) : Store × List Node :=
  let result := execProcBody proc (argLabels s args)
  (Store.set s dst (result.1 proc.ret), result.2)

def execAbstractProcCall
    (s : Store) (summary : ProcSummary) (args : List Var) (dst : Var) : Store × List Node :=
  let result := summary (argLabels s args)
  (Store.set s dst result.1, result.2)

theorem proc_call_sound
    {concrete abstract : Store}
    {proc : Proc} {summary : ProcSummary}
    {args : List Var} {dst : Var}
    (hsummary : ProcSummarySound proc summary)
    (hs : Store.le concrete abstract) :
    Store.le
      (execConcreteProcCall concrete proc args dst).1
      (execAbstractProcCall abstract summary args dst).1 /\
    ListSubset
      (execConcreteProcCall concrete proc args dst).2
      (execAbstractProcCall abstract summary args dst).2 := by
  have hargs := argLabels_sound (args := args) hs
  have hsum := hsummary (argLabels concrete args) (argLabels abstract args) hargs
  constructor
  · unfold execConcreteProcCall execAbstractProcCall
    exact Store.set_le hs hsum.left
  · unfold execConcreteProcCall execAbstractProcCall
    exact hsum.right

inductive Block where
  | instr (i : Instr) : Block
  | call (body : List Instr) (summary : Summary) : Block
  | procCall (proc : Proc) (args : List Var) (dst : Var) (summary : ProcSummary) : Block

def BlockSound : Block -> Prop
  | Block.instr _ => True
  | Block.call body summary => SummarySound body summary
  | Block.procCall proc _ _ summary => ProcSummarySound proc summary

def execConcreteBlock (s : Store) : Block -> Store × List Node
  | Block.instr i =>
      let r := step s i
      (r.store, r.violations)
  | Block.call body _summary =>
      exec s body
  | Block.procCall proc args dst _summary =>
      execConcreteProcCall s proc args dst

def execAbstractBlock (s : Store) : Block -> Store × List Node
  | Block.instr i =>
      let r := step s i
      (r.store, r.violations)
  | Block.call _body summary =>
      summary s
  | Block.procCall _proc args dst summary =>
      execAbstractProcCall s summary args dst

def execConcreteBlocks (s : Store) : List Block -> Store × List Node
  | [] => (s, [])
  | b :: rest =>
      let r := execConcreteBlock s b
      let next := execConcreteBlocks r.1 rest
      (next.1, r.2 ++ next.2)

def execAbstractBlocks (s : Store) : List Block -> Store × List Node
  | [] => (s, [])
  | b :: rest =>
      let r := execAbstractBlock s b
      let next := execAbstractBlocks r.1 rest
      (next.1, r.2 ++ next.2)

theorem block_sound
    {concrete abstract : Store} {b : Block}
    (hb : BlockSound b)
    (hs : Store.le concrete abstract) :
    Store.le (execConcreteBlock concrete b).1 (execAbstractBlock abstract b).1 /\
    ListSubset (execConcreteBlock concrete b).2 (execAbstractBlock abstract b).2 := by
  cases b with
  | instr i =>
      constructor
      · simp [execConcreteBlock, execAbstractBlock]
        exact step_store_sound (i := i) hs
      · simp [execConcreteBlock, execAbstractBlock]
        exact step_violation_sound (i := i) hs
  | call body summary =>
      exact hb concrete abstract hs
  | procCall proc args dst summary =>
      exact proc_call_sound hb hs

theorem blocks_sound
    {concrete abstract : Store} :
    forall blocks : List Block,
      (forall b, b ∈ blocks -> BlockSound b) ->
      Store.le concrete abstract ->
      Store.le (execConcreteBlocks concrete blocks).1 (execAbstractBlocks abstract blocks).1 /\
      ListSubset (execConcreteBlocks concrete blocks).2 (execAbstractBlocks abstract blocks).2 := by
  intro blocks
  induction blocks generalizing concrete abstract with
  | nil =>
      intro _ hs
      constructor
      · exact hs
      · intro id hmem
        simp [execConcreteBlocks] at hmem
  | cons b rest ih =>
      intro hall hs
      have hb : BlockSound b := hall b (by simp)
      have hfirst := block_sound hb hs
      have hrestAll : forall rb, rb ∈ rest -> BlockSound rb := by
        intro rb hr
        exact hall rb (by simp [hr])
      have htail := ih hrestAll hfirst.left
      constructor
      · simp [execConcreteBlocks, execAbstractBlocks]
        exact htail.left
      · intro id hmem
        simp [execConcreteBlocks, execAbstractBlocks] at hmem ⊢
        cases hmem with
        | inl hhead =>
            exact Or.inl (hfirst.right id hhead)
        | inr htailMem =>
            exact Or.inr (htail.right id htailMem)

theorem blocks_abstract_safety_implies_concrete_safety
    {concrete abstract : Store} {blocks : List Block}
    (hall : forall b, b ∈ blocks -> BlockSound b)
    (hs : Store.le concrete abstract)
    (habs : forall id : Node, id ∉ (execAbstractBlocks abstract blocks).2) :
    forall id : Node, id ∉ (execConcreteBlocks concrete blocks).2 := by
  intro id hbad
  exact habs id ((blocks_sound blocks hall hs).right id hbad)

/-! ## End-to-end demo -/

def emptyStore : Store :=
  fun _ => Label.clean

def vulnerableProgram : List Instr :=
  [ Instr.source 0
  , Instr.assign 1 0
  , Instr.sink 1 7
  ]

def sanitizedProgram : List Instr :=
  [ Instr.source 0
  , Instr.sanitize 1 0
  , Instr.sink 1 7
  ]

example : (exec emptyStore vulnerableProgram).2 = [7] := by
  native_decide

example : (exec emptyStore sanitizedProgram).2 = [] := by
  native_decide

example : checkSinkCert vulnerableProgram { sinkId := 7 } = true := by
  native_decide

example : checkConcreteFinding emptyStore vulnerableProgram { sinkId := 7 } = true := by
  native_decide

example : checkConcreteSafety emptyStore sanitizedProgram = true := by
  native_decide

example :
    SafeProgram emptyStore sanitizedProgram :=
  accepted_abstract_safety_gate_sound
    (concrete := emptyStore)
    (abstract := emptyStore)
    (prog := sanitizedProgram)
    (Store.le_refl emptyStore)
    (by native_decide)

def branchThenVulnerable : List Instr :=
  [ Instr.source 0
  , Instr.sink 0 9
  ]

def branchElseSafe : List Instr :=
  [ Instr.source 0
  , Instr.sanitize 1 0
  , Instr.sink 1 9
  ]

example :
    (execConcreteBranch true emptyStore branchThenVulnerable branchElseSafe).2 = [9] := by
  native_decide

example :
    (execConcreteBranch false emptyStore branchThenVulnerable branchElseSafe).2 = [] := by
  native_decide

example :
    (execAbstractBranch emptyStore branchThenVulnerable branchElseSafe).2 = [9] := by
  native_decide

example :
    forall id : Node,
      id ∉ (execConcreteBranch false emptyStore branchThenVulnerable branchElseSafe).2 :=
  branch_abstract_safety_implies_concrete_safety
    (chooseThen := false)
    (concrete := emptyStore)
    (abstract := emptyStore)
    (thenProg := branchElseSafe)
    (elseProg := branchElseSafe)
    (Store.le_refl emptyStore)
    (by native_decide)

def calleeVulnerable : List Instr :=
  [ Instr.source 2
  , Instr.sink 2 11
  ]

def callerWithSummary : List Block :=
  [ Block.call calleeVulnerable (exactSummary calleeVulnerable) ]

example :
    (execConcreteBlocks emptyStore callerWithSummary).2 = [11] := by
  native_decide

example :
    (execAbstractBlocks emptyStore callerWithSummary).2 = [11] := by
  native_decide

example :
    Store.le (execConcreteBlocks emptyStore callerWithSummary).1
      (execAbstractBlocks emptyStore callerWithSummary).1 /\
    ListSubset (execConcreteBlocks emptyStore callerWithSummary).2
      (execAbstractBlocks emptyStore callerWithSummary).2 :=
  blocks_sound
    callerWithSummary
    (by
      intro b hb
      simp [callerWithSummary] at hb
      subst hb
      exact exactSummary_sound calleeVulnerable)
    (Store.le_refl emptyStore)

def paramSinkProc : Proc :=
  { params := [0]
  , ret := 1
  , body := [Instr.assign 1 0, Instr.sink 1 13]
  }

def paramSinkSummary : ProcSummary :=
  fun _ => (Label.tainted, [13])

theorem paramSinkSummary_sound :
    ProcSummarySound paramSinkProc paramSinkSummary := by
  intro concreteArgs abstractArgs _hargs
  constructor
  · cases concreteArgs with
    | nil =>
        simp [ProcSummarySound, execProcBody, paramSinkProc, paramSinkSummary,
          bindLabels, cleanStore, exec, step, Store.set, Label.le]
    | cons arg rest =>
        cases arg <;>
          simp [ProcSummarySound, execProcBody, paramSinkProc, paramSinkSummary,
            bindLabels, cleanStore, exec, step, Store.set, Label.le]
  · intro id hmem
    cases concreteArgs with
    | nil =>
        simp [ProcSummarySound, execProcBody, paramSinkProc, paramSinkSummary,
          bindLabels, cleanStore, exec, step, Store.set] at hmem
    | cons arg rest =>
        cases arg
        · simp [ProcSummarySound, execProcBody, paramSinkProc, paramSinkSummary,
            bindLabels, cleanStore, exec, step, Store.set] at hmem
        · simp [ProcSummarySound, execProcBody, paramSinkProc, paramSinkSummary,
            bindLabels, cleanStore, exec, step, Store.set] at hmem ⊢
          exact hmem

def sourcedStore20 : Store :=
  (step emptyStore (Instr.source 20)).store

example :
    Store.le (execConcreteProcCall sourcedStore20 paramSinkProc [20] 21).1
      (execAbstractProcCall sourcedStore20 paramSinkSummary [20] 21).1 /\
    ListSubset (execConcreteProcCall sourcedStore20 paramSinkProc [20] 21).2
      (execAbstractProcCall sourcedStore20 paramSinkSummary [20] 21).2 :=
  proc_call_sound paramSinkSummary_sound (Store.le_refl sourcedStore20)

def callerWithParamSummary : List Block :=
  [ Block.instr (Instr.source 20)
  , Block.procCall paramSinkProc [20] 21 paramSinkSummary
  ]

example :
    (execConcreteBlocks emptyStore callerWithParamSummary).2 = [13] := by
  native_decide

example :
    (execAbstractBlocks emptyStore callerWithParamSummary).2 = [13] := by
  native_decide

end PcSastLean

import PcSastLean.ExtractionGate

/-!
Mini source-language extraction.

`ExtractionGate` states the important assumption: source-level claims need a
`SourceToIRSound` certificate.  This module discharges that assumption for a
small but separate source language.  The source AST and source semantics are not
defined as aliases for the IR; extraction compiles source statements into
`SInstr`, and Lean proves the compiled IR execution preserves source violations.

Claim boundary:

* Verified here: exact extraction from this mini source language to the
  context-sensitive sanitizer IR.
* External obligations: production languages still need their own syntax,
  semantics, parser/source-map correctness, and extraction proofs.
* Not modeled here: real JavaScript/TypeScript/Python control flow, objects,
  callbacks, exceptions, modules, or framework semantics.
-/

namespace PcSastLean

structure MiniSpan where
  file : Nat
  line : Nat
  col : Nat
deriving DecidableEq, Repr

inductive MiniStmtKind where
  | input (dst : Var)
  | assign (dst src : Var)
  | sanitize (dst src : Var) (kind : SinkKind)
  | concat (dst left right : Var)
  | sink (src : Var) (kind : SinkKind) (id : Node)
deriving DecidableEq, Repr

structure MiniStmt where
  span : MiniSpan
  kind : MiniStmtKind
deriving DecidableEq, Repr

def compileMiniStmtKind : MiniStmtKind -> SInstr
  | MiniStmtKind.input dst => SInstr.source dst
  | MiniStmtKind.assign dst src => SInstr.assign dst src
  | MiniStmtKind.sanitize dst src kind => SInstr.sanitize dst src kind
  | MiniStmtKind.concat dst left right => SInstr.combine dst left right
  | MiniStmtKind.sink src kind id => SInstr.sink src kind id

def compileMiniStmt (stmt : MiniStmt) : SInstr :=
  compileMiniStmtKind stmt.kind

def compileMini (prog : List MiniStmt) : List SInstr :=
  prog.map compileMiniStmt

def miniStep (s : SecStore) (stmt : MiniStmt) : SecStore × List Node :=
  match stmt.kind with
  | MiniStmtKind.input dst =>
      (s.set dst SecLabel.input, [])
  | MiniStmtKind.assign dst src =>
      (s.set dst (s src), [])
  | MiniStmtKind.sanitize dst src kind =>
      (s.set dst (SecLabel.sanitize (s src) kind), [])
  | MiniStmtKind.concat dst left right =>
      (s.set dst (SecLabel.combine (s left) (s right)), [])
  | MiniStmtKind.sink src kind id =>
      (s, if (s src).safeForBool kind then [] else [id])

def miniExec (s : SecStore) : List MiniStmt -> SecStore × List Node
  | [] => (s, [])
  | stmt :: rest =>
      let r := miniStep s stmt
      let next := miniExec r.1 rest
      (next.1, r.2 ++ next.2)

theorem miniStep_compile_exact
    (s : SecStore) (stmt : MiniStmt) :
    miniStep s stmt =
      let r := sstep s (compileMiniStmt stmt)
      (r.store, optionViolation r.violation) := by
  cases stmt with
  | mk span kind =>
      cases kind <;> simp [miniStep, compileMiniStmt, compileMiniStmtKind,
        sstep, optionViolation]
      case sink src kind id =>
        cases h : (s src).safeForBool kind <;> simp [h, optionViolation]

theorem miniExec_compile_exact
    (s : SecStore) :
    forall prog : List MiniStmt,
      miniExec s prog = sexec s (compileMini prog) := by
  intro prog
  induction prog generalizing s with
  | nil =>
      simp [miniExec, compileMini, sexec]
  | cons stmt rest ih =>
      simp [miniExec, compileMini, sexec]
      rw [miniStep_compile_exact]
      simp
      rw [ih (sstep s (compileMiniStmt stmt)).store]
      simp [compileMini]

theorem miniSourceToIRSound
    (s : SecStore) (prog : List MiniStmt) :
    SourceToIRSound (miniExec s prog).2 (sexec s (compileMini prog)).2 := by
  rw [miniExec_compile_exact]
  intro id h
  exact h

/-! ## Demo -/

def miniLoc : MiniSpan := { file := 0, line := 1, col := 1 }

def miniInput (dst : Var) : MiniStmt :=
  { span := miniLoc, kind := MiniStmtKind.input dst }

def miniSanitize (dst src : Var) (kind : SinkKind) : MiniStmt :=
  { span := miniLoc, kind := MiniStmtKind.sanitize dst src kind }

def miniConcat (dst left right : Var) : MiniStmt :=
  { span := miniLoc, kind := MiniStmtKind.concat dst left right }

def miniSink (src : Var) (kind : SinkKind) (id : Node) : MiniStmt :=
  { span := miniLoc, kind := MiniStmtKind.sink src kind id }

def miniConcatBug : List MiniStmt :=
  [ miniInput 0
  , miniConcat 2 0 1
  , miniSink 2 SinkKind.html 701
  ]

def miniConcatPatch : List MiniStmt :=
  [ miniInput 0
  , miniSanitize 3 0 SinkKind.html
  , miniConcat 2 3 1
  , miniSink 2 SinkKind.html 701
  ]

example : (miniExec emptySecStore miniConcatBug).2 = [701] := by
  native_decide

example : (sexec emptySecStore (compileMini miniConcatBug)).2 = [701] := by
  native_decide

example : (miniExec emptySecStore miniConcatPatch).2 = [] := by
  native_decide

example :
    SourceToIRSound
      (miniExec emptySecStore miniConcatPatch).2
      (sexec emptySecStore (compileMini miniConcatPatch)).2 :=
  miniSourceToIRSound emptySecStore miniConcatPatch

example :
    701 ∉ (miniExec emptySecStore miniConcatPatch).2 := by
  exact extraction_sanitizer_fix_gate
    (miniSourceToIRSound emptySecStore miniConcatPatch)
    (SecStore.sound_refl emptySecStore)
    (by native_decide)

end PcSastLean

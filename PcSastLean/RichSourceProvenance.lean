import PcSastLean.MiniSourceExtraction
import PcSastLean.SourceBackedAdapters

/-!
Rich source provenance for source-backed reports.

`SourceBackedAdapters` proves that an artifact sink can be lifted to a
source-level CI finding when a provenance certificate connects the two.  This
module enriches that certificate with source spans, AST node ids, and
generated-code origin metadata, while preserving the existing soundness theorem
by erasing rich provenance to the smaller `SourceSinkProv` interface.

Claim boundary:

* Verified here: rich source provenance can be consumed by the existing
  source-backed adapter theorem without losing soundness.
* External obligations: a real extractor must produce correct spans, AST ids,
  generated-code origins, and artifact/source links.
* Not modeled here: parser correctness, source-map correctness, macro expansion
  semantics, or template compiler semantics.
-/

namespace PcSastLean

abbrev AstNodeId := Nat

structure SourceSpan where
  start : SourceLoc
  stop : SourceLoc
deriving DecidableEq, Repr

inductive SourceOrigin where
  | direct
  | generated (generator : AstNodeId)
  | macroExpansion (macroCall : AstNodeId)
  | templateExpansion (templateNode : AstNodeId)
deriving DecidableEq, Repr

structure RichSourceSinkProv where
  sourceSink : Node
  artifactSink : Node
  astNode : AstNodeId
  span : SourceSpan
  origin : SourceOrigin
deriving DecidableEq, Repr

def RichSourceSinkProv.toBasic (p : RichSourceSinkProv) : SourceSinkProv :=
  { sourceSink := p.sourceSink
  , artifactSink := p.artifactSink
  , loc := p.span.start
  }

def RichSourceSinkProv.Sound
    (sourceViolations artifactViolations : List Node)
    (p : RichSourceSinkProv) : Prop :=
  p.sourceSink ∈ sourceViolations -> p.artifactSink ∈ artifactViolations

theorem rich_prov_erases_sound
    {sourceViolations artifactViolations : List Node}
    {p : RichSourceSinkProv}
    (h : p.Sound sourceViolations artifactViolations) :
    SourceSinkProv.Sound sourceViolations artifactViolations p.toBasic := by
  exact h

def RichSourceViolationsCoveredBy
    (sourceViolations : List Node) (p : RichSourceSinkProv) : Prop :=
  forall sink, sink ∈ sourceViolations -> sink = p.sourceSink

theorem rich_source_covered_erases
    {sourceViolations : List Node} {p : RichSourceSinkProv}
    (h : RichSourceViolationsCoveredBy sourceViolations p) :
    SourceViolationsCoveredBy sourceViolations p.toBasic := by
  exact h

def RichSourceBackedRun
    (sourceViolations artifactConcrete artifactAbstract : List Node)
    (prov : RichSourceSinkProv) : AnalyzerRun :=
  SourceBackedRun sourceViolations artifactConcrete artifactAbstract prov.toBasic

theorem richSourceBackedRun_sound
    {sourceViolations artifactConcrete artifactAbstract : List Node}
    {prov : RichSourceSinkProv}
    (hsourceCovered : RichSourceViolationsCoveredBy sourceViolations prov)
    (hanalyzer : ListSubset artifactConcrete artifactAbstract)
    (hprov : prov.Sound sourceViolations artifactConcrete) :
    (RichSourceBackedRun sourceViolations artifactConcrete artifactAbstract prov).Sound := by
  exact sourceBackedRun_sound
    (rich_source_covered_erases hsourceCovered)
    hanalyzer
    (rich_prov_erases_sound hprov)

def eraseRichProvs (provs : List RichSourceSinkProv) : List SourceSinkProv :=
  provs.map RichSourceSinkProv.toBasic

def RichSourceViolationsCoveredByAny
    (sourceViolations : List Node) (provs : List RichSourceSinkProv) : Prop :=
  forall sink, sink ∈ sourceViolations ->
    exists p, p ∈ provs /\ p.sourceSink = sink

def RichSourceProvsSound
    (sourceViolations artifactViolations : List Node)
    (provs : List RichSourceSinkProv) : Prop :=
  forall p, p ∈ provs -> p.Sound sourceViolations artifactViolations

theorem rich_covered_any_erases
    {sourceViolations : List Node} {provs : List RichSourceSinkProv}
    (h : RichSourceViolationsCoveredByAny sourceViolations provs) :
    SourceViolationsCoveredByAny sourceViolations (eraseRichProvs provs) := by
  intro sink hsink
  rcases h sink hsink with ⟨p, hp, hsource⟩
  exact ⟨p.toBasic, List.mem_map.mpr ⟨p, hp, rfl⟩, hsource⟩

theorem rich_provs_sound_erases
    {sourceViolations artifactViolations : List Node}
    {provs : List RichSourceSinkProv}
    (h : RichSourceProvsSound sourceViolations artifactViolations provs) :
    SourceProvsSound sourceViolations artifactViolations (eraseRichProvs provs) := by
  intro p hp hsource
  rcases List.mem_map.mp hp with ⟨rich, hrichMem, hrichEq⟩
  subst hrichEq
  exact h rich hrichMem hsource

def RichMultiSourceBackedRun
    (sourceViolations artifactConcrete artifactAbstract : List Node)
    (provs : List RichSourceSinkProv) : AnalyzerRun :=
  MultiSourceBackedRun sourceViolations artifactConcrete artifactAbstract
    (eraseRichProvs provs)

theorem richMultiSourceBackedRun_sound
    {sourceViolations artifactConcrete artifactAbstract : List Node}
    {provs : List RichSourceSinkProv}
    (hsourceCovered : RichSourceViolationsCoveredByAny sourceViolations provs)
    (hanalyzer : ListSubset artifactConcrete artifactAbstract)
    (hprovs : RichSourceProvsSound sourceViolations artifactConcrete provs) :
    (RichMultiSourceBackedRun sourceViolations artifactConcrete artifactAbstract provs).Sound := by
  exact multiSourceBackedRun_sound
    (rich_covered_any_erases hsourceCovered)
    hanalyzer
    (rich_provs_sound_erases hprovs)

def miniSpanToSourceSpan (span : MiniSpan) : SourceSpan :=
  { start := { file := span.file, line := span.line, col := span.col }
  , stop := { file := span.file, line := span.line, col := span.col }
  }

def miniSinkRichProv
    (stmt : MiniStmt) (astNode : AstNodeId) (artifactSink : Node) :
    Option RichSourceSinkProv :=
  match stmt.kind with
  | MiniStmtKind.sink _ _ sourceSink =>
      some
        { sourceSink := sourceSink
        , artifactSink := artifactSink
        , astNode := astNode
        , span := miniSpanToSourceSpan stmt.span
        , origin := SourceOrigin.direct
        }
  | _ => none

theorem miniSinkRichProv_source_sink
    {stmt : MiniStmt} {astNode artifactSink : Nat} {prov : RichSourceSinkProv}
    (h : miniSinkRichProv stmt astNode artifactSink = some prov) :
    exists src kind,
      stmt.kind = MiniStmtKind.sink src kind prov.sourceSink /\
      prov.artifactSink = artifactSink /\
      prov.astNode = astNode /\
      prov.origin = SourceOrigin.direct := by
  cases stmt with
  | mk span kind =>
      cases kind <;> simp [miniSinkRichProv] at h
      case sink src kind sinkId =>
        cases h
        exact ⟨src, kind, rfl, rfl, rfl, rfl⟩

def miniStmtSinkIds (stmt : MiniStmt) : List Node :=
  match stmt.kind with
  | MiniStmtKind.sink _ _ id => [id]
  | _ => []

def miniProgramSinkIds : List MiniStmt -> List Node
  | [] => []
  | stmt :: rest => miniStmtSinkIds stmt ++ miniProgramSinkIds rest

def miniStmtRichProvs (stmt : MiniStmt) (astNode : AstNodeId) : List RichSourceSinkProv :=
  match stmt.kind with
  | MiniStmtKind.sink _ _ id =>
      [ { sourceSink := id
        , artifactSink := id
        , astNode := astNode
        , span := miniSpanToSourceSpan stmt.span
        , origin := SourceOrigin.direct
        } ]
  | _ => []

def collectMiniRichProvsFrom (nextAst : AstNodeId) : List MiniStmt -> List RichSourceSinkProv
  | [] => []
  | stmt :: rest =>
      miniStmtRichProvs stmt nextAst ++ collectMiniRichProvsFrom (nextAst + 1) rest

def collectMiniRichProvs (prog : List MiniStmt) : List RichSourceSinkProv :=
  collectMiniRichProvsFrom 0 prog

theorem miniStep_violations_in_stmt_sink_ids
    (s : SecStore) (stmt : MiniStmt) :
    ListSubset (miniStep s stmt).2 (miniStmtSinkIds stmt) := by
  intro id h
  cases stmt with
  | mk span kind =>
      cases kind <;> simp [miniStep, miniStmtSinkIds] at h ⊢
      case sink src kind sinkId =>
        cases hsafe : (s src).safeForBool kind <;> simp [hsafe] at h ⊢
        exact h

theorem miniExec_violations_in_program_sink_ids
    (s : SecStore) :
    forall prog : List MiniStmt,
      ListSubset (miniExec s prog).2 (miniProgramSinkIds prog) := by
  intro prog
  induction prog generalizing s with
  | nil =>
      intro id h
      simp [miniExec] at h
  | cons stmt rest ih =>
      intro id h
      simp [miniExec, miniProgramSinkIds] at h ⊢
      cases h with
      | inl hhead =>
          exact Or.inl (miniStep_violations_in_stmt_sink_ids s stmt id hhead)
      | inr htail =>
          exact Or.inr (ih (miniStep s stmt).1 id htail)

theorem sink_id_has_rich_prov_in_stmt
    {stmt : MiniStmt} {astNode id : Nat}
    (h : id ∈ miniStmtSinkIds stmt) :
    exists p, p ∈ miniStmtRichProvs stmt astNode /\ p.sourceSink = id := by
  cases stmt with
  | mk span kind =>
      cases kind <;> simp [miniStmtSinkIds, miniStmtRichProvs] at h ⊢
      case sink src kind sinkId =>
        subst h
        simp

theorem sink_id_has_rich_prov
    {id : Node} :
    forall prog nextAst,
      id ∈ miniProgramSinkIds prog ->
      exists p, p ∈ collectMiniRichProvsFrom nextAst prog /\ p.sourceSink = id := by
  intro prog
  induction prog with
  | nil =>
      intro nextAst h
      simp [miniProgramSinkIds] at h
  | cons stmt rest ih =>
      intro nextAst h
      simp [miniProgramSinkIds] at h
      cases h with
      | inl hstmt =>
          rcases sink_id_has_rich_prov_in_stmt (stmt := stmt) (astNode := nextAst) hstmt with
            ⟨p, hp, hsource⟩
          exact ⟨p, by simp [collectMiniRichProvsFrom, hp], hsource⟩
      | inr hrest =>
          rcases ih (nextAst + 1) hrest with ⟨p, hp, hsource⟩
          exact ⟨p, by simp [collectMiniRichProvsFrom, hp], hsource⟩

theorem collected_mini_rich_provs_cover_source_violations
    (s : SecStore) (prog : List MiniStmt) :
    RichSourceViolationsCoveredByAny
      (miniExec s prog).2
      (collectMiniRichProvs prog) := by
  intro sink hsource
  have hsinkId := miniExec_violations_in_program_sink_ids s prog sink hsource
  exact sink_id_has_rich_prov (prog := prog) (nextAst := 0) hsinkId

theorem collected_mini_rich_prov_artifact_eq_source
    {p : RichSourceSinkProv} :
    forall prog nextAst,
      p ∈ collectMiniRichProvsFrom nextAst prog ->
      p.artifactSink = p.sourceSink := by
  intro prog
  induction prog with
  | nil =>
      intro nextAst h
      simp [collectMiniRichProvsFrom] at h
  | cons stmt rest ih =>
      intro nextAst h
      simp [collectMiniRichProvsFrom] at h
      cases h with
      | inl hstmt =>
          cases stmt with
          | mk span kind =>
              cases kind <;> simp [miniStmtRichProvs] at hstmt
              case sink src kind sinkId =>
                cases hstmt
                rfl
      | inr hrest =>
          exact ih (nextAst + 1) hrest

theorem collected_mini_rich_provs_sound
    (s : SecStore) (prog : List MiniStmt) :
    RichSourceProvsSound
      (miniExec s prog).2
      (sexec s (compileMini prog)).2
      (collectMiniRichProvs prog) := by
  intro p hp hsource
  have heq := collected_mini_rich_prov_artifact_eq_source
    (p := p) prog 0 hp
  rw [heq]
  exact miniSourceToIRSound s prog p.sourceSink hsource

/-! ## Demo -/

def richMiniProv701 : RichSourceSinkProv :=
  { sourceSink := 701
  , artifactSink := 701
  , astNode := 42
  , span := miniSpanToSourceSpan miniLoc
  , origin := SourceOrigin.direct
  }

theorem richMiniCovered701 :
    RichSourceViolationsCoveredBy [701] richMiniProv701 := by
  intro sink h
  simp [richMiniProv701] at h
  exact h

theorem richMiniProv701Sound :
    richMiniProv701.Sound
      (miniExec emptySecStore miniConcatBug).2
      (sexec emptySecStore (compileMini miniConcatBug)).2 := by
  intro h
  simpa [richMiniProv701] using
    (miniSourceToIRSound emptySecStore miniConcatBug 701 h)

example :
    (RichSourceBackedRun
      (miniExec emptySecStore miniConcatBug).2
      (sexec emptySecStore (compileMini miniConcatBug)).2
      (sexec emptySecStore (compileMini miniConcatBug)).2
      richMiniProv701).Sound :=
  richSourceBackedRun_sound
    (by
      intro sink h
      have hlist : (miniExec emptySecStore miniConcatBug).2 = [701] := by
        native_decide
      rw [hlist] at h
      simpa [richMiniProv701] using h)
    (by intro id h; exact h)
    richMiniProv701Sound

example :
    exists prov,
      miniSinkRichProv (miniSink 0 SinkKind.html 701) 42 701 = some prov /\
      prov.sourceSink = 701 /\
      prov.artifactSink = 701 /\
      prov.astNode = 42 := by
  refine ⟨richMiniProv701, ?_, rfl, rfl, rfl⟩
  simp [miniSinkRichProv, miniSink, richMiniProv701, miniSpanToSourceSpan, miniLoc]

example :
    RichSourceViolationsCoveredByAny
      (miniExec emptySecStore miniConcatBug).2
      (collectMiniRichProvs miniConcatBug) :=
  collected_mini_rich_provs_cover_source_violations emptySecStore miniConcatBug

example :
    RichSourceProvsSound
      (miniExec emptySecStore miniConcatBug).2
      (sexec emptySecStore (compileMini miniConcatBug)).2
      (collectMiniRichProvs miniConcatBug) :=
  collected_mini_rich_provs_sound emptySecStore miniConcatBug

example :
    (RichMultiSourceBackedRun
      (miniExec emptySecStore miniConcatBug).2
      (sexec emptySecStore (compileMini miniConcatBug)).2
      (sexec emptySecStore (compileMini miniConcatBug)).2
      (collectMiniRichProvs miniConcatBug)).Sound :=
  richMultiSourceBackedRun_sound
    (collected_mini_rich_provs_cover_source_violations emptySecStore miniConcatBug)
    (by intro id h; exact h)
    (collected_mini_rich_provs_sound emptySecStore miniConcatBug)

end PcSastLean

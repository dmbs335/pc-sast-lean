import PcSastLean.FrameworkTemplate
import PcSastLean.CIGate

/-!
Route-shadow suppression evidence.

`FrameworkTemplate` deliberately uses an abstract may-route set.  That is sound,
but it can introduce a common false positive: a parameter route appears in the
may-set even though concrete first-match routing selects a more specific literal
route.  This module proves a useful precision theorem for that case.

Claim boundary:

* Verified here: a checked route-shadow certificate proves that a finding from a
  shadowed abstract handler is not a concrete request-level bug.
* External obligations: production extractors must model route precedence,
  framework-specific matching, regex/converter constraints, middleware, and
  generated routes.
* Not modeled here: full framework dispatch or general route disjointness.
-/

namespace PcSastLean

structure RouteShadowEvidence where
  req : TemplateRequest
  concreteHandler : HandlerId
  shadowHandler : HandlerId
  sink : Node
deriving DecidableEq, Repr

def RouteShadowEvidence.Valid
    (routes : List TemplateRoute) (concrete : HandlerViolations)
    (e : RouteShadowEvidence) : Prop :=
  resolveTemplateConcrete routes e.req = some e.concreteHandler /\
  e.shadowHandler ∈ resolveTemplateAbstract routes e.req /\
  e.shadowHandler ≠ e.concreteHandler /\
  e.sink ∉ concrete e.concreteHandler

def checkRouteShadowEvidence
    (routes : List TemplateRoute) (concrete : HandlerViolations)
    (e : RouteShadowEvidence) : Bool :=
  decide (resolveTemplateConcrete routes e.req = some e.concreteHandler) &&
  decide (e.shadowHandler ∈ resolveTemplateAbstract routes e.req) &&
  decide (e.shadowHandler ≠ e.concreteHandler) &&
  decide (e.sink ∉ concrete e.concreteHandler)

theorem checkRouteShadowEvidence_sound
    {routes : List TemplateRoute} {concrete : HandlerViolations}
    {e : RouteShadowEvidence}
    (h : checkRouteShadowEvidence routes concrete e = true) :
    e.Valid routes concrete := by
  simp [checkRouteShadowEvidence, RouteShadowEvidence.Valid] at h
  exact ⟨h.left.left.left, h.left.left.right, h.left.right, h.right⟩

theorem route_shadow_not_concrete
    {routes : List TemplateRoute} {concrete : HandlerViolations}
    {e : RouteShadowEvidence}
    (h : e.Valid routes concrete) :
    e.sink ∉ execTemplateConcreteRequest routes concrete e.req := by
  intro hbad
  rcases h with ⟨hresolve, _hmay, _hshadow, hsafeConcreteHandler⟩
  unfold execTemplateConcreteRequest at hbad
  rw [hresolve] at hbad
  exact hsafeConcreteHandler hbad

theorem checked_route_shadow_not_concrete
    {routes : List TemplateRoute} {concrete : HandlerViolations}
    {e : RouteShadowEvidence}
    (h : checkRouteShadowEvidence routes concrete e = true) :
    e.sink ∉ execTemplateConcreteRequest routes concrete e.req := by
  exact route_shadow_not_concrete (checkRouteShadowEvidence_sound h)

def routeShadowTriageEvidence
    (routes : List TemplateRoute) (concrete : HandlerViolations)
    (e : RouteShadowEvidence)
    (_h : checkRouteShadowEvidence routes concrete e = true) :
    TriageEvidence :=
  { sink := e.sink
  , impossible := e.Valid routes concrete
  }

theorem routeShadowTriageEvidence_sound
    (routes : List TemplateRoute) (concrete : HandlerViolations)
    (e : RouteShadowEvidence)
    (h : checkRouteShadowEvidence routes concrete e = true) :
    EvidenceSound
      (execTemplateConcreteRequest routes concrete e.req)
      (routeShadowTriageEvidence routes concrete e h) := by
  intro hvalid
  exact route_shadow_not_concrete hvalid

/-! ## Demo: shadowed parameter-route false positive -/

def settingsShadowEvidence : RouteShadowEvidence :=
  { req := reqUserSettings
  , concreteHandler := 21
  , shadowHandler := 20
  , sink := 1201
  }

example :
    checkRouteShadowEvidence
      templateRoutes templateConcreteHandlers settingsShadowEvidence = true := by
  native_decide

example :
    1201 ∉
      execTemplateConcreteRequest templateRoutes templateConcreteHandlers reqUserSettings :=
  checked_route_shadow_not_concrete
    (routes := templateRoutes)
    (concrete := templateConcreteHandlers)
    (e := settingsShadowEvidence)
    (by native_decide)

def shadowConcreteRun : AnalyzerRun :=
  { concrete :=
      execTemplateConcreteRequest templateRoutes templateConcreteHandlers reqUserSettings
  , abstract :=
      execTemplateAbstractRequest templateRoutes templateAbstractHandlers reqUserSettings
  }

theorem shadowConcreteRunSound : shadowConcreteRun.Sound := by
  unfold shadowConcreteRun
  exact template_framework_sound
    (routes := templateRoutes)
    templateDemoHandlerSound
    reqUserSettings

def shadowTriageEvidence : TriageEvidence :=
  routeShadowTriageEvidence
    templateRoutes
    templateConcreteHandlers
    settingsShadowEvidence
    (by native_decide)

theorem shadowTriageEvidenceSound :
    EvidenceSound shadowConcreteRun.concrete shadowTriageEvidence := by
  unfold shadowConcreteRun shadowTriageEvidence
  exact routeShadowTriageEvidence_sound
    templateRoutes
    templateConcreteHandlers
    settingsShadowEvidence
    (by native_decide)

def shadowTriage : TriageRun :=
  { report := []
  , suppressed := [1201]
  , evidence := [shadowTriageEvidence]
  }

theorem shadowTriageComplete :
    shadowTriage.Complete shadowConcreteRun := by
  intro sink habs
  right
  have habsEq : sink = 1201 := by
    simpa [shadowConcreteRun, execTemplateAbstractRequest, templateRoutes,
      templateAbstractHandlers, reqUserSettings, routeUsersSettings,
      routeUsersShow, resolveTemplateAbstract, unionHandlerViolations] using habs
  subst habsEq
  constructor
  · simp [shadowTriage]
  · refine ⟨shadowTriageEvidence, ?_, ?_, ?_, ?_⟩
    · simp [shadowTriage]
    · simp [shadowTriageEvidence, routeShadowTriageEvidence, settingsShadowEvidence]
    · exact checkRouteShadowEvidence_sound (routes := templateRoutes)
        (concrete := templateConcreteHandlers)
        (e := settingsShadowEvidence)
        (by native_decide)
    · exact shadowTriageEvidenceSound

example : ListSubset shadowConcreteRun.concrete shadowTriage.report :=
  ci_gate_no_bug_hiding shadowConcreteRunSound shadowTriageComplete

end PcSastLean

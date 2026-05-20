import PcSastLean.Middleware

/-!
Framework route templates.

`Framework.lean` models routes as exact numeric keys.  This module adds a small
path-template matcher with literal and parameter segments.  Concrete routing
selects the first matching template.  Abstract extraction returns every matching
handler as a may-set.  Lean proves that the concrete selected handler is always
included in the abstract may-set.

Claim boundary:

* Verified here: path-template may-route extraction is sound for literal and
  parameter path segments in a first-match toy router.
* External obligations: production framework extractors must model regex
  routes, converters, host/subdomain routing, content negotiation, middleware
  order, generated handlers, and framework-specific precedence.
* Not modeled here: regex constraints, wildcard precedence, optional segments,
  query parameters, content negotiation, dependency injection, or redirects.
-/

namespace PcSastLean

abbrev PathAtom := Nat

inductive PathSegment where
  | lit (value : PathAtom)
  | param
deriving DecidableEq, Repr

def segmentMatches : PathSegment -> PathAtom -> Bool
  | PathSegment.lit value, atom => value == atom
  | PathSegment.param, _ => true

def templateMatches : List PathSegment -> List PathAtom -> Bool
  | [], [] => true
  | seg :: restSegs, atom :: restAtoms =>
      segmentMatches seg atom && templateMatches restSegs restAtoms
  | _, _ => false

structure TemplateRoute where
  method : HttpMethod
  template : List PathSegment
  handler : HandlerId
deriving DecidableEq, Repr

structure TemplateRequest where
  method : HttpMethod
  path : List PathAtom
deriving DecidableEq, Repr

def routeMatches (route : TemplateRoute) (req : TemplateRequest) : Bool :=
  decide (route.method = req.method) && templateMatches route.template req.path

def resolveTemplateConcrete : List TemplateRoute -> TemplateRequest -> Option HandlerId
  | [], _ => none
  | route :: rest, req =>
      if routeMatches route req then some route.handler else resolveTemplateConcrete rest req

def resolveTemplateAbstract : List TemplateRoute -> TemplateRequest -> List HandlerId
  | [], _ => []
  | route :: rest, req =>
      let tail := resolveTemplateAbstract rest req
      if routeMatches route req then route.handler :: tail else tail

def TemplateRouteExtractionSound (routes : List TemplateRoute) : Prop :=
  forall req handler,
    resolveTemplateConcrete routes req = some handler ->
    handler ∈ resolveTemplateAbstract routes req

theorem template_route_extraction_sound
    (routes : List TemplateRoute) :
    TemplateRouteExtractionSound routes := by
  intro req handler hresolve
  induction routes with
  | nil =>
      simp [resolveTemplateConcrete] at hresolve
  | cons route rest ih =>
      unfold resolveTemplateConcrete at hresolve
      unfold resolveTemplateAbstract
      by_cases hmatch : routeMatches route req = true
      · simp [hmatch] at hresolve ⊢
        exact Or.inl hresolve.symm
      · simp [hmatch] at hresolve ⊢
        exact ih hresolve

def execTemplateConcreteRequest
    (routes : List TemplateRoute) (concrete : HandlerViolations)
    (req : TemplateRequest) : List Node :=
  match resolveTemplateConcrete routes req with
  | none => []
  | some handler => concrete handler

def execTemplateAbstractRequest
    (routes : List TemplateRoute) (abstract : HandlerViolations)
    (req : TemplateRequest) : List Node :=
  unionHandlerViolations abstract (resolveTemplateAbstract routes req)

theorem template_framework_sound
    {routes : List TemplateRoute}
    {concrete abstract : HandlerViolations}
    (hhandlers : HandlerSound concrete abstract) :
    forall req,
      ListSubset
        (execTemplateConcreteRequest routes concrete req)
        (execTemplateAbstractRequest routes abstract req) := by
  intro req sink hconcrete
  unfold execTemplateConcreteRequest at hconcrete
  cases hresolve : resolveTemplateConcrete routes req with
  | none =>
      simp [hresolve] at hconcrete
  | some handler =>
      simp [hresolve] at hconcrete
      have hmay := template_route_extraction_sound routes req handler hresolve
      have habs := hhandlers handler sink hconcrete
      unfold execTemplateAbstractRequest
      exact mem_unionHandlerViolations hmay habs

theorem template_framework_fix_gate
    {routes : List TemplateRoute}
    {concrete abstract : HandlerViolations}
    {req : TemplateRequest} {sink : Node}
    (hhandlers : HandlerSound concrete abstract)
    (habs : sink ∉ execTemplateAbstractRequest routes abstract req) :
    sink ∉ execTemplateConcreteRequest routes concrete req := by
  intro hbad
  exact habs (template_framework_sound hhandlers req sink hbad)

/-! ## Demo -/

def routeUsersShow : TemplateRoute :=
  { method := HttpMethod.get
  , template := [PathSegment.lit 10, PathSegment.param]
  , handler := 20
  }

def routeUsersSettings : TemplateRoute :=
  { method := HttpMethod.get
  , template := [PathSegment.lit 10, PathSegment.lit 99]
  , handler := 21
  }

def templateRoutes : List TemplateRoute :=
  [routeUsersSettings, routeUsersShow]

def reqUser42 : TemplateRequest :=
  { method := HttpMethod.get, path := [10, 42] }

def reqUserSettings : TemplateRequest :=
  { method := HttpMethod.get, path := [10, 99] }

example : resolveTemplateConcrete templateRoutes reqUser42 = some 20 := by
  native_decide

example : resolveTemplateAbstract templateRoutes reqUser42 = [20] := by
  native_decide

example : resolveTemplateConcrete templateRoutes reqUserSettings = some 21 := by
  native_decide

example : resolveTemplateAbstract templateRoutes reqUserSettings = [21, 20] := by
  native_decide

def templateConcreteHandlers : HandlerViolations :=
  fun h => if h = 20 then [1201] else if h = 21 then [] else []

def templateAbstractHandlers : HandlerViolations :=
  fun h => if h = 20 then [1201] else if h = 21 then [] else []

theorem templateDemoHandlerSound :
    HandlerSound templateConcreteHandlers templateAbstractHandlers := by
  intro handler sink hmem
  by_cases h20 : handler = 20
  · simp [templateConcreteHandlers, templateAbstractHandlers, h20] at hmem ⊢
    exact hmem
  · by_cases h21 : handler = 21
    · simp [templateConcreteHandlers, templateAbstractHandlers, h20, h21] at hmem
    · simp [templateConcreteHandlers, h20, h21] at hmem

example :
    execTemplateConcreteRequest templateRoutes templateConcreteHandlers reqUser42 = [1201] := by
  native_decide

example :
    execTemplateAbstractRequest templateRoutes templateAbstractHandlers reqUser42 = [1201] := by
  native_decide

example :
    execTemplateConcreteRequest templateRoutes templateConcreteHandlers reqUserSettings = [] := by
  native_decide

example :
    execTemplateAbstractRequest templateRoutes templateAbstractHandlers reqUserSettings = [1201] := by
  native_decide

def templateSafeHandlers : HandlerViolations :=
  fun _ => []

theorem templateSafeHandlerSound :
    HandlerSound templateSafeHandlers templateSafeHandlers := by
  intro _ _ h
  exact h

example :
    1201 ∉ execTemplateConcreteRequest templateRoutes templateSafeHandlers reqUserSettings :=
  template_framework_fix_gate
    templateSafeHandlerSound
    (req := reqUserSettings)
    (sink := 1201)
    (by native_decide)

end PcSastLean

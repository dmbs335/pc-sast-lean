import PcSastLean.SMTCore

/-!
Framework route extraction.

Web SAST is only useful if framework routing is modeled.  A controller can be
safe in the IR and still irrelevant if the extractor missed a route, middleware
binding, or generated handler.

This module adds a small route-extraction theorem.  A concrete framework resolver
selects one handler for a request.  An abstract extractor returns a may-set of
handlers.  If the concrete handler is always included in the may-set, and handler
summaries over-approximate concrete handler violations, then request-level
concrete violations are covered by route-level abstract violations.

Claim boundary:

* Verified here: may-route extraction plus sound handler summaries cover
  request-level violations in the toy route model.
* External obligations: a framework-specific extractor must justify the may-set
  and handler summaries.
* Not modeled here: path templates, regex routing, content negotiation,
  middleware order, dependency injection, exceptions, transactions, or async
  request lifecycles.
-/

namespace PcSastLean

inductive HttpMethod where
  | get
  | post
  | put
  | delete
deriving DecidableEq, Repr

structure RouteKey where
  method : HttpMethod
  path : Nat
deriving DecidableEq, Repr

abbrev HandlerId := Nat

structure Request where
  key : RouteKey
deriving DecidableEq, Repr

structure RouteEntry where
  key : RouteKey
  handler : HandlerId
deriving DecidableEq, Repr

def resolveConcrete (routes : List RouteEntry) (req : Request) : Option HandlerId :=
  match routes with
  | [] => none
  | r :: rest => if r.key = req.key then some r.handler else resolveConcrete rest req

def resolveAbstract (routeMap : RouteKey -> List HandlerId) (req : Request) : List HandlerId :=
  routeMap req.key

def RouteExtractionSound
    (routes : List RouteEntry) (routeMap : RouteKey -> List HandlerId) : Prop :=
  forall req handler,
    resolveConcrete routes req = some handler ->
    handler ∈ resolveAbstract routeMap req

def HandlerViolations := HandlerId -> List Node

def HandlerSound (concrete abstract : HandlerViolations) : Prop :=
  forall handler, ListSubset (concrete handler) (abstract handler)

def unionHandlerViolations (abstract : HandlerViolations) : List HandlerId -> List Node
  | [] => []
  | h :: rest => abstract h ++ unionHandlerViolations abstract rest

theorem mem_unionHandlerViolations
    {abstract : HandlerViolations} {handler : HandlerId} {handlers : List HandlerId}
    {sink : Node}
    (hh : handler ∈ handlers)
    (hv : sink ∈ abstract handler) :
    sink ∈ unionHandlerViolations abstract handlers := by
  induction handlers with
  | nil =>
      simp at hh
  | cons h rest ih =>
      simp at hh
      simp [unionHandlerViolations]
      cases hh with
      | inl heq =>
          subst heq
          exact Or.inl hv
      | inr hrest =>
          exact Or.inr (ih hrest)

def execConcreteRequest
    (routes : List RouteEntry) (concrete : HandlerViolations) (req : Request) : List Node :=
  match resolveConcrete routes req with
  | none => []
  | some handler => concrete handler

def execAbstractRequest
    (routeMap : RouteKey -> List HandlerId) (abstract : HandlerViolations) (req : Request) :
    List Node :=
  unionHandlerViolations abstract (resolveAbstract routeMap req)

theorem framework_route_sound
    {routes : List RouteEntry} {routeMap : RouteKey -> List HandlerId}
    {concrete abstract : HandlerViolations}
    (hroute : RouteExtractionSound routes routeMap)
    (hhandlers : HandlerSound concrete abstract) :
    forall req, ListSubset
      (execConcreteRequest routes concrete req)
      (execAbstractRequest routeMap abstract req) := by
  intro req sink hconcrete
  unfold execConcreteRequest at hconcrete
  cases hresolve : resolveConcrete routes req with
  | none =>
      simp [hresolve] at hconcrete
  | some handler =>
      simp [hresolve] at hconcrete
      have hmay := hroute req handler hresolve
      have habs := hhandlers handler sink hconcrete
      unfold execAbstractRequest
      exact mem_unionHandlerViolations hmay habs

theorem framework_fix_gate
    {routes : List RouteEntry} {routeMap : RouteKey -> List HandlerId}
    {concrete abstract : HandlerViolations} {req : Request} {sink : Node}
    (hroute : RouteExtractionSound routes routeMap)
    (hhandlers : HandlerSound concrete abstract)
    (habs : sink ∉ execAbstractRequest routeMap abstract req) :
    sink ∉ execConcreteRequest routes concrete req := by
  intro hbad
  exact habs (framework_route_sound hroute hhandlers req sink hbad)

theorem framework_baseline_gate
    {routes : List RouteEntry} {routeMap : RouteKey -> List HandlerId}
    {concrete abstract : HandlerViolations} {req : Request} {baseline : List Node}
    (hroute : RouteExtractionSound routes routeMap)
    (hhandlers : HandlerSound concrete abstract)
    (hbaseline : ListSubset (execAbstractRequest routeMap abstract req) baseline) :
    ListSubset (execConcreteRequest routes concrete req) baseline := by
  exact ListSubset.trans (framework_route_sound hroute hhandlers req) hbaseline

/-! ## Demo -/

def routeLogin : RouteKey := { method := HttpMethod.post, path := 10 }
def routeAdmin : RouteKey := { method := HttpMethod.get, path := 20 }

def concreteRoutes : List RouteEntry :=
  [ { key := routeLogin, handler := 1 }
  , { key := routeAdmin, handler := 2 }
  ]

def abstractRouteMap : RouteKey -> List HandlerId :=
  fun key =>
    if key = routeLogin then [1]
    else if key = routeAdmin then [2, 3]
    else []

theorem demoRouteExtractionSound :
    RouteExtractionSound concreteRoutes abstractRouteMap := by
  intro req handler hresolve
  cases req with
  | mk key =>
      by_cases hLogin : key = routeLogin
      · subst hLogin
        simp [resolveConcrete, resolveAbstract, concreteRoutes, abstractRouteMap] at hresolve ⊢
        exact hresolve.symm
      · by_cases hAdmin : key = routeAdmin
        · subst hAdmin
          have hLogin' : routeLogin ≠ routeAdmin := by native_decide
          have hAdminNotLogin : routeAdmin ≠ routeLogin := by native_decide
          simp [resolveConcrete, resolveAbstract, concreteRoutes, abstractRouteMap, hLogin', hAdminNotLogin] at hresolve ⊢
          exact Or.inl hresolve.symm
        · have hLogin' : routeLogin ≠ key := by
            intro h
            exact hLogin h.symm
          have hAdmin' : routeAdmin ≠ key := by
            intro h
            exact hAdmin h.symm
          simp [resolveConcrete, concreteRoutes, hLogin', hAdmin'] at hresolve

def concreteHandlers : HandlerViolations :=
  fun h => if h = 1 then [] else if h = 2 then [91] else []

def abstractHandlers : HandlerViolations :=
  fun h => if h = 1 then [] else if h = 2 then [91] else if h = 3 then [] else []

theorem demoHandlerSound : HandlerSound concreteHandlers abstractHandlers := by
  intro handler sink hmem
  by_cases h1 : handler = 1
  · simp [concreteHandlers, abstractHandlers, h1] at hmem
  · by_cases h2 : handler = 2
    · simp [concreteHandlers, abstractHandlers, h1, h2] at hmem ⊢
      exact hmem
    · simp [concreteHandlers, h1, h2] at hmem

def loginReq : Request := { key := routeLogin }

example : execConcreteRequest concreteRoutes concreteHandlers loginReq = [] := by
  native_decide

example : execAbstractRequest abstractRouteMap abstractHandlers loginReq = [] := by
  native_decide

example : 91 ∉ execConcreteRequest concreteRoutes concreteHandlers loginReq :=
  framework_fix_gate
    demoRouteExtractionSound
    demoHandlerSound
    (req := loginReq)
    (sink := 91)
    (by native_decide)

def adminReq : Request := { key := routeAdmin }

example : execConcreteRequest concreteRoutes concreteHandlers adminReq = [91] := by
  native_decide

example : execAbstractRequest abstractRouteMap abstractHandlers adminReq = [91] := by
  native_decide

end PcSastLean

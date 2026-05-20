import PcSastLean.Framework

/-!
Middleware and authorization guard extraction.

The sound direction for middleware is subtle.  If an abstract model adds a guard
that the concrete program does not have, it may hide a real concrete path.  So we
prove the useful over-approximation direction instead:

  concrete request passes concrete middleware
  concrete middleware is included in the abstract middleware model
  =>
  abstract request passes the abstract model

Then handler findings remain over-approximating.  Any "guard blocks this path"
suppression still needs a concrete feasibility witness.
-/

namespace PcSastLean

inductive Role where
  | anon
  | user
  | admin
deriving DecidableEq, Repr

def Role.leBool (required actual : Role) : Bool :=
  match required, actual with
  | Role.anon, _ => true
  | Role.user, Role.user => true
  | Role.user, Role.admin => true
  | Role.admin, Role.admin => true
  | _, _ => false

structure Principal where
  role : Role
deriving DecidableEq, Repr

inductive Guard where
  | requireRole (role : Role)
deriving DecidableEq, Repr

def Guard.allows (p : Principal) : Guard -> Bool
  | Guard.requireRole role => Role.leBool role p.role

def guardsAllow (p : Principal) : List Guard -> Bool
  | [] => true
  | g :: rest => g.allows p && guardsAllow p rest

def GuardChainIncluded (concrete abstract : List Guard) : Prop :=
  forall g, g ∈ abstract -> g ∈ concrete

theorem guard_mem_allowed
    {p : Principal} :
    forall {guards : List Guard} {g : Guard},
      guardsAllow p guards = true ->
      g ∈ guards ->
      g.allows p = true := by
  intro guards
  induction guards with
  | nil =>
      intro g _ hmem
      simp at hmem
  | cons head tail ih =>
      intro g hallow hmem
      simp [guardsAllow] at hallow
      simp at hmem
      cases hmem with
      | inl heq =>
          subst heq
          exact hallow.left
      | inr htail =>
          exact ih hallow.right htail

theorem guardsAllow_subset
    {p : Principal} :
    forall {concrete abstract : List Guard},
      GuardChainIncluded concrete abstract ->
      guardsAllow p concrete = true ->
      guardsAllow p abstract = true := by
  intro concrete abstract hsubset hconcrete
  induction abstract with
  | nil =>
      simp [guardsAllow]
  | cons g rest ih =>
      have hgConcrete : g ∈ concrete := hsubset g (by simp)
      have hrestSubset : GuardChainIncluded concrete rest := by
        intro rg hrg
        exact hsubset rg (by simp [hrg])
      have hg : g.allows p = true := guard_mem_allowed hconcrete hgConcrete
      have hrest : guardsAllow p rest = true := ih hrestSubset
      simp [guardsAllow, hg, hrest]

def HandlerGuards := HandlerId -> List Guard

def execGuardedConcreteRequest
    (routes : List RouteEntry) (guards : HandlerGuards)
    (handlers : HandlerViolations) (principal : Principal) (req : Request) : List Node :=
  match resolveConcrete routes req with
  | none => []
  | some handler =>
      if guardsAllow principal (guards handler) then handlers handler else []

def execGuardedAbstractRequest
    (routeMap : RouteKey -> List HandlerId) (guards : HandlerGuards)
    (handlers : HandlerViolations) (principal : Principal) (req : Request) : List Node :=
  let hs := resolveAbstract routeMap req
  unionHandlerViolations
    (fun handler => if guardsAllow principal (guards handler) then handlers handler else [])
    hs

def GuardExtractionSound
    (concreteGuards abstractGuards : HandlerGuards) : Prop :=
  forall handler,
    GuardChainIncluded (concreteGuards handler) (abstractGuards handler)

theorem guarded_framework_sound
    {routes : List RouteEntry} {routeMap : RouteKey -> List HandlerId}
    {concreteHandlers abstractHandlers : HandlerViolations}
    {concreteGuards abstractGuards : HandlerGuards}
    (hroute : RouteExtractionSound routes routeMap)
    (hguards : GuardExtractionSound concreteGuards abstractGuards)
    (hhandlers : HandlerSound concreteHandlers abstractHandlers) :
    forall principal req,
      ListSubset
        (execGuardedConcreteRequest routes concreteGuards concreteHandlers principal req)
        (execGuardedAbstractRequest routeMap abstractGuards abstractHandlers principal req) := by
  intro principal req sink hconcrete
  unfold execGuardedConcreteRequest at hconcrete
  cases hresolve : resolveConcrete routes req with
  | none =>
      simp [hresolve] at hconcrete
  | some handler =>
      by_cases hallow : guardsAllow principal (concreteGuards handler) = true
      · simp [hresolve, hallow] at hconcrete
        have hmay := hroute req handler hresolve
        have habsHandler := hhandlers handler sink hconcrete
        have habsAllow : guardsAllow principal (abstractGuards handler) = true :=
          guardsAllow_subset (hguards handler) hallow
        unfold execGuardedAbstractRequest
        exact mem_unionHandlerViolations hmay (by simp [habsAllow, habsHandler])
      · simp [hresolve, hallow] at hconcrete

/-! ## Demo -/

def anonPrincipal : Principal := { role := Role.anon }
def adminPrincipal : Principal := { role := Role.admin }

def demoConcreteGuards : HandlerGuards :=
  fun h => if h = 2 then [Guard.requireRole Role.admin] else []

def demoAbstractGuards : HandlerGuards :=
  fun h => if h = 2 then [Guard.requireRole Role.admin] else []

theorem demoGuardExtractionSound :
    GuardExtractionSound demoConcreteGuards demoAbstractGuards := by
  intro handler g hg
  by_cases h2 : handler = 2
  · simp [demoConcreteGuards, demoAbstractGuards, h2] at hg ⊢
    exact hg
  · simp [demoAbstractGuards, h2] at hg

example :
    execGuardedConcreteRequest concreteRoutes demoConcreteGuards concreteHandlers
      anonPrincipal adminReq = [] := by
  native_decide

example :
    execGuardedConcreteRequest concreteRoutes demoConcreteGuards concreteHandlers
      adminPrincipal adminReq = [91] := by
  native_decide

example :
    ListSubset
      (execGuardedConcreteRequest concreteRoutes demoConcreteGuards concreteHandlers
        adminPrincipal adminReq)
      (execGuardedAbstractRequest abstractRouteMap demoAbstractGuards abstractHandlers
        adminPrincipal adminReq) :=
  guarded_framework_sound
    demoRouteExtractionSound
    demoGuardExtractionSound
    demoHandlerSound
    adminPrincipal
    adminReq

end PcSastLean

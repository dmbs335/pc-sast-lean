import PcSastLean.Middleware

/-!
Template rendering contexts.

XSS analysis is not just "HTML safe or unsafe".  Template slots have contexts:
HTML text, HTML attribute, JavaScript string, URL attribute, and so on.  This
module connects template slots to the context-sensitive sanitizer lattice.
-/

namespace PcSastLean

inductive TemplateContext where
  | htmlText
  | htmlAttr
  | jsString
  | urlAttr
deriving DecidableEq, Repr

def TemplateContext.requiredSink : TemplateContext -> SinkKind
  | TemplateContext.htmlText => SinkKind.html
  | TemplateContext.htmlAttr => SinkKind.html
  | TemplateContext.jsString => SinkKind.shell
  | TemplateContext.urlAttr => SinkKind.path

structure TemplateSlot where
  value : Var
  context : TemplateContext
  sink : Node
deriving DecidableEq, Repr

def renderSlotViolation (s : SecStore) (slot : TemplateSlot) : Option Node :=
  if (s slot.value).safeForBool slot.context.requiredSink then none else some slot.sink

def renderTemplate (s : SecStore) : List TemplateSlot -> List Node
  | [] => []
  | slot :: rest => optionViolation (renderSlotViolation s slot) ++ renderTemplate s rest

theorem render_slot_safe
    {s : SecStore} {slot : TemplateSlot}
    (h : (s slot.value).safeForBool slot.context.requiredSink = true) :
    renderSlotViolation s slot = none := by
  simp [renderSlotViolation, h]

theorem render_slot_violation
    {s : SecStore} {slot : TemplateSlot}
    (h : (s slot.value).safeForBool slot.context.requiredSink = false) :
    renderSlotViolation s slot = some slot.sink := by
  simp [renderSlotViolation, h]

theorem template_fix_gate
    {s : SecStore} {slots : List TemplateSlot} {sink : Node}
    (h : sink ∉ renderTemplate s slots) :
    sink ∉ renderTemplate s slots := h

/-! ## Demo -/

def templateStoreHtmlOnly : SecStore :=
  SecStore.set emptySecStore 0 (SecLabel.sanitize SecLabel.input SinkKind.html)

def templateStoreUrlSafe : SecStore :=
  SecStore.set emptySecStore 0 (SecLabel.sanitize SecLabel.input SinkKind.path)

def urlSlot : TemplateSlot :=
  { value := 0, context := TemplateContext.urlAttr, sink := 101 }

def htmlSlot : TemplateSlot :=
  { value := 0, context := TemplateContext.htmlText, sink := 102 }

example : renderTemplate templateStoreHtmlOnly [urlSlot] = [101] := by
  native_decide

example : renderTemplate templateStoreHtmlOnly [htmlSlot] = [] := by
  native_decide

example : renderTemplate templateStoreUrlSafe [urlSlot] = [] := by
  native_decide

theorem html_sanitizer_not_url_safe :
    ¬ (templateStoreHtmlOnly 0).safeFor TemplateContext.urlAttr.requiredSink := by
  intro h
  simp [templateStoreHtmlOnly, SecStore.set, SecLabel.sanitize, SecLabel.input,
    SecLabel.safeFor, TemplateContext.requiredSink, Protection.add, Protection.has] at h
  cases h

end PcSastLean

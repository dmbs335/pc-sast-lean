import PcSastLean.Template

/-!
ORM and SQL query construction.

SQLi modeling is not just "SQL sanitizer exists".  Prepared parameters are safe
because values are bound out-of-band; string concatenation is unsafe unless the
value has SQL protection.  This module captures that distinction.
-/

namespace PcSastLean

inductive QueryPart where
  | lit : QueryPart
  | concatValue (v : Var) : QueryPart
  | paramValue (v : Var) : QueryPart
deriving DecidableEq, Repr

def queryPartViolation (s : SecStore) (sink : Node) : QueryPart -> Option Node
  | QueryPart.lit => none
  | QueryPart.paramValue _ => none
  | QueryPart.concatValue v =>
      if (s v).safeForBool SinkKind.sql then none else some sink

def renderQuery (s : SecStore) (sink : Node) : List QueryPart -> List Node
  | [] => []
  | p :: rest => optionViolation (queryPartViolation s sink p) ++ renderQuery s sink rest

theorem prepared_param_no_violation
    {s : SecStore} {sink : Node} {v : Var} :
    queryPartViolation s sink (QueryPart.paramValue v) = none := by
  simp [queryPartViolation]

theorem concat_value_safe_if_sql_safe
    {s : SecStore} {sink : Node} {v : Var}
    (h : (s v).safeForBool SinkKind.sql = true) :
    queryPartViolation s sink (QueryPart.concatValue v) = none := by
  simp [queryPartViolation, h]

theorem concat_value_violation_if_not_sql_safe
    {s : SecStore} {sink : Node} {v : Var}
    (h : (s v).safeForBool SinkKind.sql = false) :
    queryPartViolation s sink (QueryPart.concatValue v) = some sink := by
  simp [queryPartViolation, h]

/-! ## Demo -/

def sqlInputStore : SecStore :=
  SecStore.set emptySecStore 0 SecLabel.input

def sqlSafeStore : SecStore :=
  SecStore.set emptySecStore 0 (SecLabel.sanitize SecLabel.input SinkKind.sql)

def concatQuery : List QueryPart :=
  [ QueryPart.lit, QueryPart.concatValue 0 ]

def preparedQuery : List QueryPart :=
  [ QueryPart.lit, QueryPart.paramValue 0 ]

example : renderQuery sqlInputStore 111 concatQuery = [111] := by
  native_decide

example : renderQuery sqlInputStore 111 preparedQuery = [] := by
  native_decide

example : renderQuery sqlSafeStore 111 concatQuery = [] := by
  native_decide

theorem prepared_binding_fix_gate :
    111 ∉ renderQuery sqlInputStore 111 preparedQuery := by
  native_decide

theorem sql_sanitizer_concat_fix_gate :
    111 ∉ renderQuery sqlSafeStore 111 concatQuery := by
  native_decide

end PcSastLean

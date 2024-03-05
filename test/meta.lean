import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Meta.Basic
import Mathlib.Tactic.Relation.Rfl

/-! # Tests for mathlib extensions to `Lean.Expr` and `Lean.Meta` -/

namespace Tests

open Lean Meta

private axiom test_sorry : ∀ {α}, α
set_option pp.unicode.fun true

def eTrue := Expr.const ``True []
def eFalse := Expr.const ``False []
def eNat := Expr.const ``Nat []
def eNatZero := Expr.const ``Nat.zero []
def eNatOne := mkApp (Expr.const ``Nat.succ []) eNatZero

/-! ### `Lean.Expr.getAppApps` -/

#guard Expr.getAppApps (.const `f []) == #[]
#guard Expr.getAppApps (mkAppN (.const `f []) #[eTrue]) == #[.app (.const `f []) eTrue]
#guard Expr.getAppApps (mkAppN (.const `f []) #[eTrue, eFalse]) ==
        #[.app (.const `f []) eTrue, .app (.app (.const `f []) eTrue) eFalse]

/-! ### `Lean.Expr.reduceProjStruct?` -/

/-- info: none -/
#guard_msgs in #eval Expr.reduceProjStruct? eTrue
/-- info: none -/
#guard_msgs in #eval Expr.reduceProjStruct? (.const ``Prod.fst [levelOne, levelOne])
/-- info: some (Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])) -/
#guard_msgs in #eval Expr.reduceProjStruct? <|
  mkAppN (.const ``Prod.fst [levelOne, levelOne])
    #[eNat, eNat, mkAppN (.const ``Prod.mk [levelOne, levelOne]) #[eNat, eNat, eNatOne, eNatZero]]
/-- info: some (Lean.Expr.const `Nat.zero []) -/
#guard_msgs in #eval Expr.reduceProjStruct? <|
  mkAppN (.const ``Prod.snd [levelOne, levelOne])
    #[eNat, eNat, mkAppN (.const ``Prod.mk [levelOne, levelOne]) #[eNat, eNat, eNatOne, eNatZero]]
/--
error: ill-formed expression, Prod.fst is the 1-th projection function
but Prod.mk does not have enough arguments
-/
#guard_msgs (error, drop info) in #eval Expr.reduceProjStruct? <|
  mkAppN (.const ``Prod.fst [levelOne, levelOne])
    #[eNat, eNat, mkAppN (.const ``Prod.mk [levelOne, levelOne]) #[eNat, eNat]]

/-! ### `Lean.Expr.forallNot_of_notExists` -/

open Elab Tactic in
elab "test_forallNot_of_notExists" t:term : tactic => do
  let e ← elabTerm t none
  let ety ← instantiateMVars (← inferType e)
  let .app (.const ``Not []) ety' := ety | throwError "Type of expression must be not"
  let (ety', e') ← Expr.forallNot_of_notExists ety' e
  unless ← isDefEq ety' (← inferType e') do throwError "bad proof"
  logInfo m!"{ety'}"

/-- info: ∀ (x : Nat), ¬0 < x -/
#guard_msgs in
example (h : ¬ ∃ x, 0 < x) : False := by
  test_forallNot_of_notExists h
  exact test_sorry

/-- info: ∀ (x x_1 : Nat), ¬x_1 < x -/
#guard_msgs in
example (h : ¬ ∃ x y : Nat, y < x) : False := by
  test_forallNot_of_notExists h
  exact test_sorry

/-- error: failed -/
#guard_msgs in
example (h : ¬ 0 < 1) : False := by
  test_forallNot_of_notExists h

/-! ### `Lean.Meta.mkRel` -/

/-- info: true -/
#guard_msgs in
#eval do return (← mkRel ``Eq eNatZero eNatOne) == (← mkAppM ``Eq #[eNatZero, eNatOne])

/-- info: true -/
#guard_msgs in
#eval do return (← mkRel ``Iff eTrue eFalse) == (← mkAppM ``Iff #[eTrue, eFalse])

/-- info: true -/
#guard_msgs in
#eval do return (← mkRel ``HEq eTrue eFalse) == (← mkAppM ``HEq #[eTrue, eFalse])

/-- info: true -/
#guard_msgs in
#eval do return (← mkRel ``LT.lt eNatZero eNatOne) == (← mkAppM ``LT.lt #[eNatZero, eNatOne])

/-! ### `Lean.Expr.relSidesIfRefl?` -/

/--
info: some (`Eq, Lean.Expr.const `Nat.zero [],
Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero []))
-/
#guard_msgs in #eval do Expr.relSidesIfRefl? (← mkRel ``Eq eNatZero eNatOne)

/-- info: some (`Iff, Lean.Expr.const `True [], Lean.Expr.const `False []) -/
#guard_msgs in #eval do Expr.relSidesIfRefl? (← mkRel ``Iff eTrue eFalse)

/-- info: some (`HEq, Lean.Expr.const `True [], Lean.Expr.const `False []) -/
#guard_msgs in #eval do Expr.relSidesIfRefl? (← mkRel ``HEq eTrue eFalse)

/-- info: none -/
#guard_msgs in #eval do Expr.relSidesIfRefl? (← mkRel ``LT.lt eNatZero eNatOne)

attribute [refl] Nat.le_refl

/--
info: some (`LE.le, Lean.Expr.const `Nat.zero [],
Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero []))
-/
#guard_msgs in #eval do Expr.relSidesIfRefl? (← mkRel ``LE.le eNatZero eNatOne)

end Tests

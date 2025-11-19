/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


/-! # A tactic for proving algebraic goals in a field

This file contains the `field` tactic, a finishing tactic which roughly consists of running
`field_simp; ring1`.

-/

open Lean Meta Qq

namespace Mathlib.Tactic.FieldSimp

open Lean Elab Tactic Lean.Parser.Tactic

/--
The `field` tactic proves equality goals in (semi-)fields. For example:
```
example {x y : ℚ} (hx : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by
  field
example {a b : ℝ} (ha : a ≠ 0) : a / (a * b) - 1 / b = 0 := by field
```
The scope of the tactic is equality goals which are *universal*, in the sense that they are true in
any field in which the appropriate denominators don't vanish. (That is, they are consequences purely
of the field axioms.)

Checking the nonvanishing of the necessary denominators is done using a variety of tricks -- in
particular this part of the reasoning is non-universal, i.e. can be specific to the field at hand
(order properties, explicit `≠ 0` hypotheses, `CharZero` if that is known, etc).  The user can also
provide additional terms to help with the nonzeroness proofs. For example:
```
example {K : Type*} [Field K] (hK : ∀ x : K, x ^ 2 + 1 ≠ 0) (x : K) :
    1 / (x ^ 2 + 1) + x ^ 2 / (x ^ 2 + 1) = 1 := by
  field [hK]
```

The `field` tactic is built from the tactics `field_simp` (which clears the denominators) and `ring`
(which proves equality goals universally true in commutative (semi-)rings). If `field` fails to
prove your goal, you may still be able to prove your goal by running the `field_simp` and `ring_nf`
normalizations in some order.  For example, this statement:
```
example {a b : ℚ} (H : b + a ≠ 0) : a / (a + b) + b / (b + a) = 1
```
is not proved by `field` but is proved by `ring_nf at *; field`. -/
elab (name := field) "field" d:(ppSpace discharger)? args:(ppSpace simpArgs)? : tactic =>
    withMainContext do
  let disch ← parseDischarger d args
  let s0 ← saveState
  -- run `field_simp` (only at the top level, not recursively)
  liftMetaTactic1 (transformAtTarget ((AtomM.run .reducible ∘ reduceProp disch) ·) "field"
    (failIfUnchanged := False) · default)
  let s1 ← saveState
  try
    -- run `ring1`
    liftMetaFinishingTactic fun g ↦ AtomM.run .reducible <| Ring.proveEq g
  catch e =>
    try
      -- If `field` doesn't solve the goal, we first backtrack to the situation at the time of the
      -- `field_simp` call, and suggest `field_simp` if `field_simp` does anything useful.
      s0.restore
      let tacticStx ← `(tactic| field_simp $(d)? $(args)?)
      evalTactic tacticStx
      Meta.Tactic.TryThis.addSuggestion (← getRef) tacticStx
    catch _ =>
      -- If `field_simp` also doesn't do anything useful (maybe there are no denominators in the
      -- goal), then we backtrack to where the `ring1` call failed, and report that error message.
      s1.restore
      throw e

end Mathlib.Tactic.FieldSimp

open Mathlib TacticAnalysis

/-- Look for `field` invocations on which the (generally more lightweight) `ring` tactic suffices.
-/
register_option linter.tacticAnalysis.fieldToRing : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.fieldToRing, inherit_doc linter.tacticAnalysis.fieldToRing]
def fieldToRing : TacticAnalysis.Config :=
  terminalReplacement "field" "ring" ``Mathlib.Tactic.FieldSimp.field (fun _ _ _ => `(tactic| ring))
    (reportFailure := false) (reportSuccess := true) (reportSlowdown := true)
    (maxSlowdown := 1000)

/-- Look for terminal `field_simp` invocations which can be replaced by the more compact `field`.
-/
register_option linter.tacticAnalysis.fieldSimpToField : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.fieldSimpToField,
  inherit_doc linter.tacticAnalysis.fieldSimpToField]
def fieldSimpToField : TacticAnalysis.Config :=
  terminalReplacement "field_simp" "field" ``Mathlib.Tactic.FieldSimp.fieldSimp
    (fun _ _ stx => do
    match stx with
    | `(tactic| field_simp $(disch)? $(args)? $(loc)?) =>
      match loc with
      | some loc =>
        match Elab.Tactic.expandLocation loc with
        | .targets #[] true => `(tactic| field $(disch)? $(args)?)
        | _ => pure ⟨Syntax.missing⟩
      | none => `(tactic| field $(disch)? $(args)?)
    | _ => throwError "could not parse the field_simp")
    (reportFailure := false) (reportSuccess := true) (reportSlowdown := true)
    (maxSlowdown := 1000)

/-- Look for `field_simp; ring` invocations which can be replaced by the more compact `field`.
-/
register_option linter.tacticAnalysis.fieldSimpRingToField : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.fieldSimpRingToField,
  inherit_doc linter.tacticAnalysis.fieldSimpRingToField]
def fieldSimpRingToField : TacticAnalysis.Config := .ofComplex {
  out := Option (TSyntax `tactic)
  ctx :=
    Option (TSyntax `Lean.Parser.Tactic.discharger) × Option (TSyntax `Lean.Parser.Tactic.simpArgs)
  trigger ctx stx :=
    match stx with
    | `(tactic| field_simp $(disch)? $(args)?) => .continue (disch, args)
    | `(tactic| ring) => if let some zz := ctx then .accept zz else .skip
    | _ => .skip
  test ctxI i ctx goal := do
    let (disch, args) := ctx
    let tac ← `(tactic| field $(disch)? $(args)?)
    try
      let _ ← ctxI.runTacticCode i goal tac
      return some tac
    catch _e => -- if for whatever reason the replacement doesn't work
      return none
  tell _stx _old _oldHeartbeats new _newHeartbeats :=
    pure <| if let some tac := new then m!"Try this: {tac}" else none}

/-! We register `field` with the `hint` tactic. -/
register_hint 850 field

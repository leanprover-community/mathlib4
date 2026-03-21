/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring.Basic


/-! # A tactic for proving algebraic goals in a field

This file contains the `field` tactic, a finishing tactic which roughly consists of running
`field_simp; ring1`.

-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.FieldSimp

open Lean Elab Tactic Lean.Parser.Tactic

/--
`field` solves equality goals in (semi-)fields. The goal must be an equality which is *universal*,
in the sense that it is true in any field in which the appropriate denominators don't vanish.
(That is, it is a consequence purely of the field axioms.)

The `field` tactic is built from the tactics `field_simp` (which clears the denominators) and `ring`
(which proves equality goals universally true in commutative (semi-)rings). If `field` fails to
prove your goal, you may still be able to prove your goal by running the `field_simp` and `ring_nf`
normalizations in some order.

The tactic will try discharge proofs of nonzeroness of denominators, and skip steps if discharging
fails. These denominators are made out of denominators appearing in the input expression, by
repeatedly taking products or divisors. The default discharger can be non-universal, i.e. can be
specific to the field at hand (order properties, explicit `≠ 0` hypotheses, `CharZero` if that is
known, etc). See `Mathlib.Tactic.FieldSimp.discharge` for full details of the default discharger
algorithm.

* `field (disch := tac)` uses the tactic sequence `tac` to discharge nonzeroness proofs.
* `field [t₁, ..., tₙ]` provides terms `t₁`, ..., `tₙ` to the discharger for nonzeroness proofs.

Examples:
```
example {x y : ℚ} (hx : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by field
example {a b : ℝ} (ha : a ≠ 0) : a / (a * b) - 1 / b = 0 := by field

-- The user can also provide additional terms to help with nonzeroness proofs:
example {K : Type*} [Field K] (hK : ∀ x : K, x ^ 2 + 1 ≠ 0) (x : K) :
    1 / (x ^ 2 + 1) + x ^ 2 / (x ^ 2 + 1) = 1 := by
  field [hK]

example {a b : ℚ} (H : b + a ≠ 0) : a / (a + b) + b / (b + a) = 1 := by
  -- `field` cannot prove this on its own.
  fail_if_success field
  -- But running `ring_nf` and `field_simp` in a different order works:
  ring_nf at *
  field
```

-/
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

/-! We register `field` with the `hint` tactic. -/
register_hint 850 field
register_try?_tactic (priority := 850) field

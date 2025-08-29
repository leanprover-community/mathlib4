/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, David Renshaw, Heather Macbeth, Michael Rothgang
-/
import Mathlib.Tactic.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for the `field_simp` and `field` tactics
-/

private axiom test_sorry : ∀ {α}, α

open Lean Elab Tactic in
elab "test_field_simp" : tactic => do
  evalTactic <| ← `(tactic | field_simp)
  liftMetaFinishingTactic fun g ↦ do
    let ty ← g.getType
    logInfo ty
    g.assign (← Meta.mkAppOptM ``test_sorry #[ty])

set_option linter.unusedVariables false

/-! ## Documenting "field_simp normal form" -/
section

variable {P : ℚ → Prop} {x y z : ℚ}

/-- error: field_simp made no progress on goal -/
#guard_msgs in
example : P (1 : ℚ) := by test_field_simp

/-! ### One atom -/

/-- info: P 1 -/
#guard_msgs in
example : P (x ^ 0) := by test_field_simp

/-- info: P x -/
#guard_msgs in
example : P (x ^ 1) := by test_field_simp

/-- error: field_simp made no progress on goal -/
#guard_msgs in
example : P x := by test_field_simp

/-- info: P (x ^ 2) -/
#guard_msgs in
example : P (x ^ 2) := by test_field_simp

/-- info: P (x ^ 3) -/
#guard_msgs in
example : P (x ^ 1 * x ^ 2) := by test_field_simp

/-- info: P (x ^ 2) -/
#guard_msgs in
example : P (x * x) := by test_field_simp

/-- info: P (x ^ 45) -/
#guard_msgs in
example : P (x ^ 3 * x ^ 42) := by test_field_simp

/-- info: P (x ^ k * x ^ 2) -/
#guard_msgs in
example {k : ℤ} : P (x ^ k * x ^ 2) := by test_field_simp

/-- info: P (1 / x ^ 3) -/
#guard_msgs in
example : P (x ^ (-1 : ℤ) * x ^ (-2 : ℤ)) := by test_field_simp

-- Cancellation: if x could be zero, we cannot cancel x * x⁻¹.

/-- info: P (1 / x) -/
#guard_msgs in
example : P (x⁻¹) := by test_field_simp

/-- info: P (x / x) -/
#guard_msgs in
example : P (x * x⁻¹) := by test_field_simp

/-- info: P (x / x) -/
#guard_msgs in
example : P (x⁻¹ * x) := by test_field_simp

/-- info: P x -/
#guard_msgs in
example : P (x * x * x⁻¹) := by test_field_simp

/-- info: P (x / x) -/
#guard_msgs in
example : P (x / x) := by test_field_simp

/-- info: P x -/
#guard_msgs in
example : P (x ^ 2 * x⁻¹) := by test_field_simp

/-- info: P (x ^ 2) -/
#guard_msgs in
example : P (x ^ 3 * x⁻¹) := by test_field_simp

/-- info: P (1 / x ^ 3) -/
#guard_msgs in
example : P (x / x ^ 4) := by test_field_simp

/-- info: P (x ^ 6) -/
#guard_msgs in
example : P ((x ^ (2:ℤ)) ^ 3) := by test_field_simp

/-- info: P (1 / x ^ 6) -/
#guard_msgs in
example : P ((x ^ (-2:ℤ)) ^ 3) := by test_field_simp

-- Even if we cannot cancel, we can simplify the exponent.

/-- info: P (x / x) -/
#guard_msgs in
example : P (x ^ 2 * x ^ (-2 : ℤ)) := by test_field_simp

/-- info: P (x / x) -/
#guard_msgs in
example : P (x ^ (-37 : ℤ) * x ^ 37) := by test_field_simp

-- If x is non-zero, we do cancel.

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x * x⁻¹) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x⁻¹ * x) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x ^ (-17 : ℤ) * x ^ 17) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x ^ 17 / x ^ 17) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x / x) := by test_field_simp

/-- info: P (x ^ 2) -/
#guard_msgs in
example {hx : x ≠ 0} : P (x ^ 3 * x⁻¹) := by test_field_simp

/-- info: P (1 / x ^ 3) -/
#guard_msgs in
example {hx : x ≠ 0} : P (x / x ^ 4) := by test_field_simp

-- When a term is subtracted from itself,
-- we normalize to the product of the common factor with a difference of constants.
-- The old (pre-2025) `field_simp` implementation subsumed `simp`,
-- so it would clean up such terms further.
-- But such simplifications are not necessarily in scope for `field_simp`.

/-- info: P (x * (1 - 1)) -/
#guard_msgs in
example : P (x - x) := by test_field_simp

/-- info: P (x * (-1 + 1)) -/
#guard_msgs in
example : P (-x + x) := by test_field_simp

/-- info: P (x * (1 - 1)) -/
#guard_msgs in
example : P (1 * x - x) := by test_field_simp

/-- info: P (2 * (1 - 1) * x) -/
#guard_msgs in
example : P ((2 - 2) * x) := by test_field_simp

/-- info: P (↑a * x * (1 - 1)) -/
#guard_msgs in
example {a : Nat} : P (a* x - a * x) := by test_field_simp

/-! ### Two atoms -/

/-- error: field_simp made no progress on goal -/
#guard_msgs in
example : P (x + y) := by test_field_simp

/-- info: P (x * y) -/
#guard_msgs in
example : P (x * y) := by test_field_simp

/-- info: P (1 / (x * y)) -/
#guard_msgs in
example : P ((x * y)⁻¹) := by test_field_simp

/-- info: P (x * y / (x * y)) -/
#guard_msgs in
example : P ((x * y) / (y * x)) := by test_field_simp

/-- info: P (x * y * (1 + 1)) -/
#guard_msgs in
example : P (x * y + y * x) := by test_field_simp

/-- info: P (x * (y + 1)) -/
#guard_msgs in
example : P (x * y + x * 1) := by test_field_simp

/-- info: P (x * y / (x * y)) -/
#guard_msgs in
example : P ((x * y) * (y * x)⁻¹) := by test_field_simp

/-- info: P y -/
#guard_msgs in
example : P (x ^ (0:ℤ) * y) := by test_field_simp

/-- info: P (y ^ 2) -/
#guard_msgs in
example : P (y * (y + x) ^ (0:ℤ) * y) := by test_field_simp

/-- info: P (x / y) -/
#guard_msgs in
example : P (x / y) := by test_field_simp

/-- info: P (-(x / y)) -/
#guard_msgs in
example : P (x / -y) := by test_field_simp

/-- info: P (-(x / y)) -/
#guard_msgs in
example : P (-x / y) := by test_field_simp

/-- info: P ((x + (x + 1) * y / (y + 1)) / (x + 1)) -/
#guard_msgs in
example (hx : x + 1 ≠ 0) : P (x / (x + 1) + y / (y + 1)) := by test_field_simp

/-- info: P ((x * (y + 1) + (x + 1) * y) / ((x + 1) * (y + 1))) -/
#guard_msgs in
example (hx : 0 < x + 1) (hy : 0 < y + 1) : P (x / (x + 1) + y / (y + 1)) := by test_field_simp

/-- info: P (x ^ 2 / y) -/
#guard_msgs in
example : P (x / (y / x)) := by test_field_simp

/-- info: P (x ^ 2 * y ^ 3) -/
#guard_msgs in
example : P (x / (y ^ (-3:ℤ) / x)) := by test_field_simp

/-- info: P (x ^ 2 * y ^ 3) -/
#guard_msgs in
example : P ((x / y ^ (-3:ℤ)) * x) := by test_field_simp

/-- info: P (x ^ 3 * y ^ 4) -/
#guard_msgs in
example : P (x ^ 1 * y * x ^ 2 * y ^ 3) := by test_field_simp

/-- info: P (x ^ 3 * y / y) -/
#guard_msgs in
example : P (x ^ 1 * y * x ^ 2 * y⁻¹) := by test_field_simp

/-- info: P (1 / y) -/
#guard_msgs in
example (hx : x ≠ 0) : P (x / (x * y)) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example (hx : x ≠ 0) (hy : y ≠ 0) : P ((x * y) / (y * x)) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example (hx : x ≠ 0) (hy : y ≠ 0) : P ((x * y) * (y * x)⁻¹) := by test_field_simp

/-- info: P (x ^ 3) -/
#guard_msgs in
example (hy : y ≠ 0) : P (x ^ 1 * y * x ^ 2 * y⁻¹) := by test_field_simp

/-! ### Three atoms -/

/-- info: P (x * y * z) -/
#guard_msgs in
example : P (x * y * z) := by test_field_simp

/-- info: P (x * (y + z)) -/
#guard_msgs in
example : P (x * y + x * z) := by test_field_simp

/-- info: P (1 / (y + z)) -/
#guard_msgs in
example (hx : x ≠ 0) : P (x / (x * y + x * z))  := by test_field_simp

/-- info: P (x / (x * (y + z))) -/
#guard_msgs in
example : P (x / (x * y + x * z))  := by test_field_simp

/-! ### Constants and addition/subtraction -/

-- We do not simplify literals.

/-- info: P (x * (2 - 1)) -/
#guard_msgs in
example : P (2 * x - 1 * x) := by test_field_simp

/-- info: P (x * (2 - 1 - 1)) -/
#guard_msgs in
example : P (2 * x - x - x) := by test_field_simp

/-- info: P (x * (2 - 1)) -/
#guard_msgs in
example : P (2 * x - x) := by test_field_simp

/-- info: P (x * (3 - 2 - 1)) -/
#guard_msgs in
example : P ((3 - 2) * x - x) := by test_field_simp

-- There is no special handling of zero,
-- in particular multiplication with a zero literal is not simplified.

/-- info: P (0 * x) -/
#guard_msgs in
example : P (0 * x) := by test_field_simp

/-- info: P (0 * (x * y + 1)) -/
#guard_msgs in
example : P (0 * x * y + 0) := by test_field_simp

/-- info: P (x * y * (1 - 1) * z) -/
#guard_msgs in
example : P ((x * y - y * x) * z) := by test_field_simp

-- Iterated negation is simplified.
/-- info: P x -/
#guard_msgs in
example : P (-(-x)) := by test_field_simp

-- Subtraction from zero is not simplified.
/-- info: P (0 - (0 + -x)) -/
#guard_msgs in
example : P (0 -(0 + (-x))) := by test_field_simp

/-! ### Transparency

As is standard in Mathlib tactics for algebra, `field_simp` respects let-bindings and identifies
atoms only up to reducible defeq. -/

/-- info: P (x * (y + a)) -/
#guard_msgs in
example : True := by
  let a := y
  suffices P (x * y + x * a) from test_sorry
  test_field_simp

/-- info: P (x * y * (1 + 1)) -/
#guard_msgs in
example : P (x * y + x * (fun t ↦ t) y) := by test_field_simp

/-- info: P (x * (y + id y)) -/
#guard_msgs in
example : P (x * y + x * id y) := by test_field_simp

end

/-! ## Cancel denominators from equalities -/

/-! ### Finishing tactic

The `field` tactic is a finishing tactic for equalities in fields.
Effectively it runs `field_simp` to clear denominators, then hands the result to `ring1`.
-/

example : (1:ℚ) / 3 + 1 / 6 = 1 / 2 := by field
example {x : ℚ} (hx : x ≠ 0) : x * x⁻¹ = 1 := by field
example {a b : ℚ} (h : b ≠ 0) : a / b + 2 * a / b + (-a) / b + (- (2 * a)) / b = 0 := by field

-- example from the `field` docstring
example {x y : ℚ} (hx : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by field

example {x : ℚ} : x ^ 2 / (x ^ 2 + 1) + 1 / (x ^ 2 + 1) = 1 := by field

example {x y : ℚ} (hx : 0 < x) :
    ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)) ^ 2 + (2 * x * y / (x ^ 2 + y ^ 2)) ^ 2 = 1 := by
  field

example {K : Type*} [Field K] (a b c d x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x ^ 2 + d / x ^ 3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field

-- example from the `field` docstring
example {a b : ℚ} (ha : a ≠ 0) : a / (a * b) - 1 / b = 0 := by field

example {x : ℚ} : x ^ 2 * x⁻¹ = x := by field

-- example from `field` docstring
example {K : Type*} [Field K] (hK : ∀ x : K, x ^ 2 + 1 ≠ 0) (x : K) :
    1 / (x ^ 2 + 1) + x ^ 2 / (x ^ 2 + 1) = 1 := by
  field [hK]

-- `field` will suggest `field_simp` on failure, if `field_simp` does anything.
/--
info: Try this: field_simp
---
error: unsolved goals
x y z : ℚ
hx : x + y ≠ 0
⊢ 1 = z
-/
#guard_msgs in
example {x y z : ℚ} (hx : x + y ≠ 0) : x / (x + y) + y / (x + y) = z := by field

-- If `field` fails but `field_simp` also fails, we just throw an error.
/--
error: ring failed, ring expressions not equal
x y z : ℚ
⊢ x + y = z
-/
#guard_msgs in
example {x y z : ℚ} : x + y = z := by field

/-
The `field` tactic differs slightly from `field_simp; ring1` in that it clears denominators only at
the top level, not recursively in subexpressions.

(`ring1` acts only at the top level, so for consistency we also clear denominators only at the top
level.) -/
/--
info: Try this: field_simp
---
error: unsolved goals
a b : ℚ
f : ℚ → ℚ
⊢ f (a * b) * (1 - 1) = 0
-/
#guard_msgs in
example (a b : ℚ) (f : ℚ → ℚ) : f (a ^ 2 * b / a) - f (b ^ 2 * a / b) = 0 := by field

-- (Compare with the example above: this is out of scope for `field`.)
example (a b : ℚ) (f : ℚ → ℚ) : f (a ^ 2 * b / a) - f (b ^ 2 * a / b) = 0 := by
  field_simp
  ring1

-- `field` does not fully clear denominators in these examples, but calling different normalizations
-- in succession eventually succeeds.

-- This example is used in the `field` docstring.
example {a b : ℚ} (H : b + a ≠ 0) : a / (a + b) + b / (b + a) = 1 := by
  ring_nf at *
  field

/--
info: Try this: field_simp
---
error: unsolved goals
a b : ℚ
H : b + a ≠ 0
⊢ (a + b) / (a + b) = 1
-/
#guard_msgs in
example {a b : ℚ} (H : b + a ≠ 0) : a / (a + b) + b / (b + a) = 1 := by
  ring_nf
  field

/--
info: Try this: field_simp
---
error: unsolved goals
a b : ℚ
H : b + a ≠ 0
⊢ a * (b + a) / (a + b) + b = b + a
-/
#guard_msgs in
example {a b : ℚ} (H : b + a ≠ 0) : a / (a + b) + b / (b + a) = 1 := by
  field

example {a b : ℚ} (H : a + b + 1 ≠ 0) :
    a / (a + (b + 1) ^ 2 / (b + 1)) + (b + 1) / (b + a + 1) = 1 := by
  field_simp
  ring_nf at *
  field

/--
info: Try this: field_simp
---
error: unsolved goals
a b : ℚ
H : 1 + a + b ≠ 0
⊢ a * (1 + a + b) / (a + b * 2 / (1 + b) + b ^ 2 / (1 + b) + 1 / (1 + b)) + b + 1 = 1 + a + b
-/
#guard_msgs in
example {a b : ℚ} (H : a + b + 1 ≠ 0) :
    a / (a + (b + 1) ^ 2 / (b + 1)) + (b + 1) / (b + a + 1) = 1 := by
  ring_nf at *
  field

/--
info: Try this: field_simp
---
error: unsolved goals
a b : ℚ
H : a + b + 1 ≠ 0
⊢ a / (a + (b + 1)) + (b + 1) / (b + a + 1) = 1
-/
#guard_msgs in
example {a b : ℚ} (H : a + b + 1 ≠ 0) :
    a / (a + (b + 1) ^ 2 / (b + 1)) + (b + 1) / (b + a + 1) = 1 := by
  field

/-! ### Mid-proof use -/

example {K : Type*} [Semifield K] (x y : K) (hy : y + 1 ≠ 0) : 2 * x / (y + 1) = x := by
  field_simp
  guard_target = 2 * x = x * (y + 1)
  exact test_sorry

example {K : Type*} [Semifield K] (x y : K) : 2 * x / (y + 1) = x := by
  have hy : y + 1 ≠ 0 := test_sorry -- test mdata, context updating, etc
  field_simp
  guard_target = 2 * x = x * (y + 1)
  exact test_sorry

example {x y z w : ℚ} (h : x / y = z / w) (hy : y ≠ 0) (hw : w ≠ 0) : True := by
  field_simp at h
  guard_hyp h : x * w = y * z
  exact trivial

example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  field_simp
  guard_target = x = (1 - y + y) * z
  exact test_sorry

example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  simp [field]
  guard_target = x = z
  exact test_sorry

example {x y z : ℚ} (hy : y ≠ 0) (hz : z ≠ 0) : x / y = x / z := by
  field_simp
  guard_target = x * z = x * y
  exact test_sorry

example {x y z : ℚ} (hy : y ≠ 0) (hz : z ≠ 0) (hx : x ≠ 0) : x / y = x / z := by
  field_simp
  guard_target = z = y
  exact test_sorry

example {x y z : ℚ} (h : x * y = x * z) : True := by
  field_simp at h
  guard_hyp h : x * y = x * z
  exact trivial

-- used in `field_simp` docstring
example {K : Type*} [Field K] {x : K} (hx : x ^ 5 = 1) (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) :
    (x + 1 / x) ^ 2 + (x + 1 / x) = 1 := by
  field_simp
  guard_target = (x ^ 2 + 1) * (x ^ 2 + 1 + x) = x ^ 2
  calc
    (x ^ 2 + 1) * (x ^ 2 + 1 + x) = (x ^ 5 - 1) / (x - 1) + x ^ 2 := by field
    _ = x ^ 2 := by simp [hx]

-- used in `field` simproc docstring
example {K : Type*} [Field K] {x : K} (hx : x ^ 5 = 1) (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) :
    (x + 1 / x) ^ 2 + (x + 1 / x) = 1 := by
  simp only [field]
  guard_target = (x ^ 2 + 1) * (x ^ 2 + 1 + x) = x ^ 2
  calc
    (x ^ 2 + 1) * (x ^ 2 + 1 + x) = (x ^ 5 - 1) / (x - 1) + x ^ 2 := by field
    _ = x ^ 2 := by simp [hx]

section

-- TODO (new implementation): do we want `field_simp` to reduce this to `⊢ x * y = z * y ^ 2`?
-- Or perhaps to `⊢ x / y / y = z / y`?
example {x y z : ℚ} : x / y ^ 2 = z / y := by
  field_simp
  guard_target = x / y ^ 2 = z / y
  exact test_sorry

-- why the first idea could work
example {x y z : ℚ} : (x / y ^ 2 = z / y) ↔ (x * y = z * y ^ 2) := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  field_simp

-- why the second idea could work
example {x y z : ℚ} : (x / y ^ 2 = z / y) ↔ (x / y / y = z / y) := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  ring_nf

end

/-! From PluenneckeRuzsa: new `field_simp` doesn't handle variable exponents -/

example (x y : ℚ≥0) (n : ℕ) (hx : x ≠ 0) : y * ((y / x) ^ n * x) = (y / x) ^ (n + 1) * x * x := by
  field_simp
  guard_target =  y * (y / x) ^ n = x * (y / x) ^ (n + 1)
  exact test_sorry

example (x y : ℚ≥0) (n : ℕ) (hx : x ≠ 0) : y * ((y / x) ^ n * x) = (y / x) ^ (n + 1) * x * x := by
  simp [field, pow_add]

/-

/-- Specify a simp config. -/
-- this feature was dropped in the August 2025 `field_simp` refactor
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  fail_if_success field_simp (maxSteps := 0)
  field_simp (config := {})
  ring

-/

/-! ### check that `field_simp` closes goals when the equality reduces to an identity -/

example {x y : ℚ} (h : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by field_simp
example {x : ℚ} (hx : x ≠ 0) : x * x⁻¹ = 1 := by field_simp
example {x : ℚ} : x ^ 2 * x⁻¹ = x := by field_simp

/-! TODO: cancel denominators from disequalities and inequalities -/

-- example (hx : x ≠ 0) (h : x ^ 2 * x⁻¹ ≠ x) : True := by field_simp at h

/-! ## Tactic operating recursively -/

example {x y : ℚ} (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (x * y / y) / f (x / y * y) = 1 := by
  field_simp [hf]

-- test for consistent atom ordering across subterms
example {x y : ℚ} (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (y * x * y / y) / f (x * y / y * y) = 1 := by
  field_simp [hf]

example {x y z : ℚ} (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (y * x / (y ^ 2 / z)) / f (z / (y / x)) = 1 := by
  field_simp [hf]

open Finset in
example (n : ℕ) : ∏ i ∈ range n, (1 - (i + 2 : ℚ)⁻¹) < 1 := by
  field_simp
  guard_target = ∏ x ∈ range n, ((x:ℚ) + 2 - 1) / (x + 2) < 1
  exact test_sorry

/-! ## Performance -/

-- from `InnerProductGeometry.cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle`
-- old implementation: 19983 heartbeats!!!
-- new implementation: 2979 heartbeats
example {V : Type*} [AddCommGroup V] (F : V → ℚ)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxn : F x ≠ 0) (hyn : F y ≠ 0) (hxyn : F (x - y) ≠ 0) :
    (F x * F x - (F x * F x + F y * F y - F (x - y) * F (x - y)) / 2) / (F x * F (x - y))
      * ((F y * F y - (F x * F x + F y * F y - F (x - y) * F (x - y)) / 2) / (F y * F (x - y)))
      * F x * F y * F (x - y) * F (x - y)
    - (F x * F x * (F y * F y)
      - (F x * F x + F y * F y - F (x - y) * F (x - y)) / 2
        * ((F x * F x + F y * F y - F (x - y) * F (x - y)) / 2))
    = -((F x * F x + F y * F y - F (x - y) * F (x - y)) / 2 / (F x * F y))
        * F x * F y * F (x - y) * F (x - y) := by
  field_simp
  exact test_sorry

/-! ## Discharger -/

/--
Test that the discharger can clear nontrivial denominators in ℚ.
-/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  field_simp
  ring

/-- Use a custom discharger -/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  field_simp (discharger := simp; assumption)
  ring

/-- warning: Custom `field_simp` dischargers do not make use of the `field_simp` arguments list -/
#guard_msgs in
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  field_simp (discharger := simp; assumption) [h₀]
  ring

-- mimic discharger
example {K : Type*} [Field K] (n : ℕ) (w : K) (h0 : w ≠ 0) : w ^ n ≠ 0 := by simp [h0]

example {K : Type*} [Field K] (n : ℕ) (w : K) (h0 : w ≠ 0) : w ^ n / w ^ n = n := by
  field_simp
  guard_target = (1:K) = n
  exact test_sorry

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

-- mimic discharger
example  (hK : ∀ ξ : K, ξ + 1 ≠ 0) (x : K) : |x + 1| ≠ 0 := by simp [hK x]

example  (hK : ∀ ξ : K, ξ + 1 ≠ 0) (x : K) : 1 / |x + 1| = 5 := by
  field_simp [hK x]
  guard_target = 1 = |x + 1| * 5
  exact test_sorry

/-! the `positivity` part of the discharger can't take help from user-provided terms -/

-- mimic discharger
/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : x + 1 ≠ 0 := by positivity

/--
error: unsolved goals
K : Type u_1
inst✝² : Field K
inst✝¹ : LinearOrder K
inst✝ : IsStrictOrderedRing K
hK : ∀ (ξ : K), 0 < ξ + 1
x : K
⊢ 1 / (x + 1) = 5
-/
#guard_msgs in
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by field_simp [hK x]

-- works when the hypothesis is brought out for use by `positivity`
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by
  have := hK x
  field_simp
  guard_target = 1 = (x + 1) * 5
  exact test_sorry

end

/- Bug (some would say "feature") of the old implementation: the implementation used the
`field_simp` discharger on the side conditions of other simp-lemmas, not just the `field_simp` simp
set.

Such behaviour can be invoked in the new implementation by running `simp` with the `field_simp`
simprocs and a discharger.
-/

example (m n : ℕ) (h : m ≤ n) (hm : (2:ℚ) < n - m) : (n:ℚ) / (n - m) = 1 / ↑(n - m) * n := by
  simp [field]
  guard_target = (n:ℚ) = ↑n * (↑n - ↑m) / ↑(n - m)
  exact test_sorry

example (m n : ℕ) (h : m ≤ n) (hm : (2:ℚ) < n - m) : (n:ℚ) / (n - m) = 1 / ↑(n - m) * n := by
  simp (disch := assumption) [field]

/-! ### Non-confluence issues

We need to ensure that the "normal form" of the simproc `field` does not conflict with the direction
of any Mathlib simp-lemmas, otherwise we can get infinite loops.  -/

-- Mathlib simp-lemmas `neg_mul` and `mul_neg`
example {K : Type*} [Field K] {a b c x : K} : -(c * a * x) + -b = 7 := by
  simp [field]
  fail_if_success rw [neg_mul]
  fail_if_success rw [mul_neg]
  exact test_sorry

-- Mathlib simp-lemma `one_div`
example (a b : ℚ) : a * b⁻¹ = 7 := by
  simp [field]
  fail_if_success rw [one_div]
  exact test_sorry

-- Mathlib simp-lemma `mul_inv_rev`
-- from `Analysis.SpecialFunctions.Stirling`
example (m n : ℚ) : (m * n)⁻¹ = 7 := by
  simp [field]
  fail_if_success rw [mul_inv_rev]
  exact test_sorry

-- undiagnosed non-confluence
-- from `LinearAlgebra.QuadraticForm.Real`
/--
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example {t : ℚ} (ht : t ≠ 0) (a : ∀ t, t ≠ 0 → ℚ) : (if h : t = 0 then 1 else a t h) = 1 := by
  simp only [field]

/-! ## Units of a ring, partial division

This feature was dropped in the August 2025 `field_simp` refactor.
-/

/-

/-
Check that `field_simp` works for units of a ring.
-/

section CommRing
variable {R : Type*} [CommRing R] (a b c d e f g : R) (u₁ u₂ : Rˣ)

/--
Check that `divp_add_divp_same` takes priority over `divp_add_divp`.
-/
example : a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁ := by field_simp

/--
Check that `divp_sub_divp_same` takes priority over `divp_sub_divp`.
-/
example : a /ₚ u₁ - b /ₚ u₁ = (a - b) /ₚ u₁ := by field_simp

/-
Combining `eq_divp_iff_mul_eq` and `divp_eq_iff_mul_eq`.
-/
example : a /ₚ u₁ = b /ₚ u₂ ↔ a * u₂ = b * u₁ := by field_simp

/--
Making sure inverses of units are rewritten properly.
-/
example : ↑u₁⁻¹ = 1 /ₚ u₁ := by field_simp

/--
Checking arithmetic expressions.
-/
example : (f - (e + c * -(a /ₚ u₁) * b + d) - g) =
    (f * u₁ - (e * u₁ + c * (-a) * b + d * u₁) - g * u₁) /ₚ u₁ := by field_simp

/--
Division of units.
-/
example : a /ₚ (u₁ / u₂) = a * u₂ /ₚ u₁ := by field_simp

example : a /ₚ u₁ /ₚ u₂ = a /ₚ (u₂ * u₁) := by field_simp

end CommRing

-/

/-! ## Algebraic structures weaker than `Field` -/

example {K : Type} [CommGroupWithZero K] {x y : K} : y / x * x ^ 3 * y ^ 3 = x ^ 2 * y ^ 5 / y := by
  field_simp

example {K : Type} [Semifield K] {x y : K} (h : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by
  field_simp

/-! ## Miscellaneous -/

-- An example of "unfolding" `field_simps` to its "definition"
example {aa : ℚ} (ha : (aa : ℚ) ≠ 0) (hb : 2 * aa = 3) : (1 : ℚ) / aa = 2/ 3 := by
  simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, field_simps]
  rw [hb]

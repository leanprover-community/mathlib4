/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, David Renshaw, Heather Macbeth, Michael Rothgang
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for the `field_simp` tactic
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

/-- error: simp made no progress -/
#guard_msgs in
example : P (1 : ℚ) := by test_field_simp

/- ### One atom -/

/-- info: P 1 -/
#guard_msgs in
example : P (x ^ 0) := by test_field_simp

/-- info: P x -/
#guard_msgs in
example : P (x ^ 1) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P x := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x ^ 2) := by test_field_simp

/-- info: P (x * x ^ 2) -/
#guard_msgs in
example : P (x ^ 1 * x ^ 2) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x * x) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x ^ 3 * x ^ 42) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example {k : ℤ} : P (x ^ k * x ^ 2) := by test_field_simp

/-- info: P (1 / (x * x ^ 2)) -/
#guard_msgs in
example : P (x ^ (-1 : ℤ) * x ^ (-2 : ℤ)) := by test_field_simp

-- Cancellation: if x could be zero, we cannot cancel x * x⁻¹.

/-- info: P (x / x) -/
#guard_msgs in
example : P (x * x⁻¹) := by test_field_simp

/-- info: P (x / x) -/
#guard_msgs in
example : P (x⁻¹ * x) := by test_field_simp

/-- info: P x -/
#guard_msgs in
example : P (x * x * x⁻¹) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x / x) := by test_field_simp

-- TODO (new implementation): this should reduce to `P x`
/-- info: P (x ^ 2 / x) -/
#guard_msgs in
example : P (x ^ 2 * x⁻¹) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (x ^ 2)`
/-- info: P (x ^ 3 / x) -/
#guard_msgs in
example : P (x ^ 3 * x⁻¹) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (1 / x ^ 2)`
/-- error: simp made no progress -/
#guard_msgs in
example : P (x / x ^ 4) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (1 / x ^ 6)`
/-- info: P (1 / (x ^ 2) ^ 3) -/
#guard_msgs in
example : P ((x ^ (-2:ℤ)) ^ 3) := by test_field_simp

-- If x is non-zero, we do cancel.

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x * x⁻¹) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x⁻¹ * x) := by test_field_simp

/-- info: P 1 -/
#guard_msgs in
example {hx : x ≠ 0} : P (x / x) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (x ^ 2)`
/-- info: P (x ^ 3 / x) -/
#guard_msgs in
example {hx : x ≠ 0} : P (x ^ 3 * x⁻¹) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (1 / x ^ 2)`
/-- error: simp made no progress -/
#guard_msgs in
example {hx : x ≠ 0} : P (x / x ^ 4) := by test_field_simp

/- ### Two atoms -/

/-- error: simp made no progress -/
#guard_msgs in
example : P (x + y) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x * y) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P ((x * y) / (y * x)) := by test_field_simp

/-- info: P (x * y + x) -/
#guard_msgs in
example : P (x * y + x * 1) := by test_field_simp

/-- info: P (x * y / (y * x)) -/
#guard_msgs in
example : P ((x * y) * (y * x)⁻¹) := by test_field_simp

/-- info: P y -/
#guard_msgs in
example : P (x ^ (0:ℤ) * y) := by test_field_simp

/-- info: P (y * y) -/
#guard_msgs in
example : P (y * (y + x) ^ (0:ℤ) * y) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x / y) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x / -y) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (-x / y) := by test_field_simp

/-- info: P ((x + y * (x + 1) / (y + 1)) / (x + 1)) -/
#guard_msgs in
example (hx : x + 1 ≠ 0) : P (x / (x + 1) + y / (y + 1)) := by test_field_simp

/-- info: P ((x * (y + 1) + y * (x + 1)) / ((x + 1) * (y + 1))) -/
#guard_msgs in
example (hx : 0 < x + 1) (hy : 0 < y + 1) : P (x / (x + 1) + y / (y + 1)) := by test_field_simp

-- TODO (new implementation): exploit `AtomM` to combine like terms, i.e. `x * y * x` to `x ^ 2 * y`

/-- info: P (x * x / y) -/
#guard_msgs in
example : P (x / (y / x)) := by test_field_simp

/-- info: P (x * (y ^ 3 * x)) -/
#guard_msgs in
example : P (x / (y ^ (-3:ℤ) / x)) := by test_field_simp

/-- info: P (x * y ^ 3 * x) -/
#guard_msgs in
example : P ((x / y ^ (-3:ℤ)) * x) := by test_field_simp

/-- info: P (x * y * x ^ 2 * y ^ 3) -/
#guard_msgs in
example : P (x ^ 1 * y * x ^ 2 * y ^ 3) := by test_field_simp

/-- info: P (x * y * x ^ 2 / y) -/
#guard_msgs in
example : P (x ^ 1 * y * x ^ 2 * y⁻¹) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (1 / y)`
/-- error: simp made no progress -/
#guard_msgs in
example (hx : x ≠ 0) : P (x / (x * y)) := by test_field_simp

-- TODO (new implementation): this should reduce to `P 1`
/-- error: simp made no progress -/
#guard_msgs in
example (hx : x ≠ 0) (hy : y ≠ 0) : P ((x * y) / (y * x)) := by test_field_simp

-- TODO (new implementation): this should reduce to `P 1`
/-- info: P (x * y / (y * x)) -/
#guard_msgs in
example (hx : x ≠ 0) (hy : y ≠ 0) : P ((x * y) * (y * x)⁻¹) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (x ^ 3)`
/-- info: P (x * y * x ^ 2 / y) -/
#guard_msgs in
example (hy : y ≠ 0) : P (x ^ 1 * y * x ^ 2 * y⁻¹) := by test_field_simp

/- ### Three atoms -/

/-- error: simp made no progress -/
#guard_msgs in
example : P (x * y * z) := by test_field_simp

/-- error: simp made no progress -/
#guard_msgs in
example : P (x * y + x * z) := by test_field_simp

-- TODO (new implementation): this should reduce to `P (1 / (y + z))`
/-- error: simp made no progress -/
#guard_msgs in
example (hx : x ≠ 0) : P (x / (x * y + x * z))  := by test_field_simp

-- TODO (new implementation): this should reduce to `P (x / (x * (y + z)))`
/-- error: simp made no progress -/
#guard_msgs in
example : P (x / (x * y + x * z))  := by test_field_simp

end

/-! ## Cancel denominators from equalities -/

/-! ### Most common use case: Cancel denominators to something solvable by `ring`

When (eventually) this is robust enough, there should be a `field` tactic
-/

macro "field" : tactic => `(tactic | (try field_simp) <;> ring1)

example : (1:ℚ) / 3 + 1 / 6 = 1 / 2 := by field
example {x : ℚ} (hx : x ≠ 0) : x * x⁻¹ = 1 := by field
example {a b : ℚ} (h : b ≠ 0) : a / b + 2 * a / b + (-a) / b + (- (2 * a)) / b = 0 := by field
example {x y : ℚ} (hx : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by field

example {x y : ℚ} (hx : 0 < x) :
    ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)) ^ 2 + (2 * x * y / (x ^ 2 + y ^ 2)) ^ 2 = 1 := by
  field

-- TODO (new implementation): `field` should solve this, no `b ≠ 0` hypothesis required
/--
error: ring failed, ring expressions not equal
a b : ℚ
ha : a ≠ 0
⊢ a * a⁻¹ * b⁻¹ - b⁻¹ = 0
-/
#guard_msgs in
example {a b : ℚ} (ha : a ≠ 0) : a / (a * b) - 1 / b = 0 := by field

-- TODO (new implementation): `field` should solve this, no `x ≠ 0` hypothesis required
/--
error: ring failed, ring expressions not equal
x : ℚ
⊢ x ^ 2 * x⁻¹ = x
-/
#guard_msgs in
example {x : ℚ} : x ^ 2 * x⁻¹ = x := by field

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
  guard_hyp h : x * w = z * y
  exact trivial

example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  field_simp
  guard_target = x = z
  exact test_sorry

-- TODO: this annoyance happens often, fix it (want `⊢ x * z = x * y`)
-- it is bad behaviour since is does not preserve the property "goal is an equality"
-- `mul_eq_zero` is already on the `fieldSimpExcluded` list and this example suggests that
-- `mul_eq_mul_left_iff` should be too
example {x y z : ℚ} (hy : y ≠ 0) (hz : z ≠ 0) : x / y = x / z := by
  field_simp
  guard_target = z = y ∨ x = 0
  exact test_sorry

-- TODO (new implementation): here `z ≠ 0`; would be nice to get `⊢ z = y`, not `⊢ x * z = x * y`
example {x y z : ℚ} (hy : y ≠ 0) (hz : z ≠ 0) (hx : x ≠ 0) : x / y = x / z := by
  field_simp
  guard_target = z = y ∨ x = 0
  exact test_sorry

-- TODO: this annoyance happens often, fix it (want "no progress")
-- it is bad behaviour since is does not preserve the property "`h` is an equality"
-- `mul_eq_zero` is already on the `fieldSimpExcluded` list and this example suggests that
-- `mul_eq_mul_left_iff` should be too
example {x y z : ℚ} (h : x * y = x * z) : True := by
  field_simp at h
  guard_hyp h : y = z ∨ x = 0
  exact trivial

section

-- TODO (new implementation): do we want `field_simp` to reduce this to `⊢ x * y = z * y ^ 2`?
-- Or perhaps to `⊢ x / y / y = z / y`?
/-- error: simp made no progress -/
#guard_msgs in
example {x y z : ℚ} : x / y ^ 2 = z / y := by
  field_simp

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

-- from PluenneckeRuzsa
example (x y : ℚ≥0) (n : ℕ) (hx : x ≠ 0) : y * ((y / x) ^ n * x) = (y / x) ^ (n + 1) * x * x := by
  field_simp
  ring

/-- Specify a simp config. -/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  fail_if_success field_simp (maxSteps := 0)
  field_simp (config := {})
  ring

/- ### check that `field_simp` closes goals when the equality reduces to an identity -/

example {x y : ℚ} (h : x + y ≠ 0) : x / (x + y) + y / (x + y) = 1 := by field_simp
example {x : ℚ} (hx : x ≠ 0) : x * x⁻¹ = 1 := by field_simp
example {a b : ℚ} (h : b ≠ 0) : a / b + 2 * a / b + (-a) / b - (2 * a) / b = 0 := by field_simp

/-! TODO: cancel denominators from disequalities and inequalities -/

-- example (hx : x ≠ 0) (h : x ^ 2 * x⁻¹ ≠ x) : True := by field_simp at h

/-! ## Tactic operating recursively -/

example {x y : ℚ} (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (x * y / y) / f (x / y * y) = 1 := by
  field_simp [hf]

-- TODO (new implementation): with consistent atom ordering this problem would be solved
/--
error: unsolved goals
x y : ℚ
hx : y ≠ 0
f : ℚ → ℚ
hf : ∀ (t : ℚ), f t ≠ 0
⊢ f (y * x) = f (x * y)
-/
#guard_msgs in
example {x y : ℚ} (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (y * x * y / y) / f (x * y / y * y) = 1 := by
  field_simp [hf]

-- TODO (new implementation): this problem should be solved
/--
error: unsolved goals
x y z : ℚ
hx : y ≠ 0
f : ℚ → ℚ
hf : ∀ (t : ℚ), f t ≠ 0
⊢ f (y * x * z / y ^ 2) = f (z * x / y)
-/
#guard_msgs in
example {x y z : ℚ} (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (y * x / (y ^ 2 / z)) / f (z / (y / x)) = 1 := by
  field_simp [hf]

/-! ## Performance -/

-- from `InnerProductGeometry.cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle`
-- 21794 heartbeats!!!
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
  guard_target =
    ((F x * F x * 2 - (F x * F x + F y * F y - F (x - y) * F (x - y)))
      * (F y * F y * 2 - (F x * F x + F y * F y - F (x - y) * F (x - y)))
      * F x * F y * F (x - y) * F (x - y) * (2 * 2)
      - 2 * (F x * F (x - y)) * (2 * (F y * F (x - y))) *
        (F x * F x * (F y * F y) * (2 * 2)
        - (F x * F x + F y * F y - F (x - y) * F (x - y))
        * (F x * F x + F y * F y - F (x - y) * F (x - y))))
    * (2 * (F x * F y))
    = (F (x - y) * F (x - y) - (F x * F x + F y * F y))
      * F x * F y * F (x - y) * F (x - y)
      * (2 * (F x * F (x - y)) * (2 * (F y * F (x - y))) * (2 * 2))
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
  guard_target = 1 = 5 * |x + 1|
  exact test_sorry

/-! the `positivity` part of the discharger can't take help from user-provided terms -/

-- mimic discharger
/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : x + 1 ≠ 0 := by positivity

/-- error: simp made no progress -/
#guard_msgs in
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by field_simp [hK x]

-- works when the hypothesis is brought out for use by `positivity`
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by
  have := hK x
  field_simp
  guard_target = 1 = 5 * (x + 1)
  exact test_sorry

end

/- Bug (some would say "feature"): the implementation uses the `field_simp` discharger on the side
conditions of other simp-lemmas, not just the `field_simp` simp set. -/
example (m n : ℕ) (h : m ≤ n) (hm : (2:ℚ) < n - m) : (n:ℚ) / (n - m) = 1 / ↑(n - m) * n := by
  field_simp

/-! ## Units of a ring, partial division -/

/-
Check that `field_simp` works for units of a ring.
-/

variable {R : Type _} [CommRing R] (a b c d e f g : R) (u₁ u₂ : Rˣ)

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

-- TODO (new implementation): handle `CommGroupWithZero`, not just `Semifield`

/-! ## Miscellaneous -/

-- An example of "unfolding" `field_simps` to its "definition"
example {aa : ℚ} (ha : (aa : ℚ) ≠ 0) (hb : 2 * aa = 3) : (1 : ℚ) / aa = 2/ 3 := by
  simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, field_simps]
  rw [hb]

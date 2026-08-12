/-
Copyright (c) 2026 Brandon Frederick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brandon Frederick
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The AM-HM inequality

This file proves the arithmetic mean-harmonic mean inequality in the division-free form

`(#s) ^ 2 ≤ (∑ i ∈ s, z i) * (∑ i ∈ s, (z i)⁻¹)`

for positive `z`, together with its two- and three-term specializations, and derives
Nesbitt's inequality as a corollary.

## Implementation notes

Everything here holds in a linearly ordered semifield with `ExistsAddOfLE`, so in particular
over `ℚ≥0` and `NNReal`. Semifields have no subtraction, so the usual sum-of-squares argument
is unavailable; the substitute is `two_mul_le_add_sq`, the division-free AM-GM for linearly
ordered commutative semirings. Dividing it by `x * y` gives `two_le_div_add_div`, and summing
that over a `Finset` is the whole content of the general inequality.

Mathlib's other mean inequalities (`Real.inner_le_nnorm_mul_nnorm`-style AM-GM and HM-GM in
`Mathlib/Analysis/MeanInequalities.lean`) go through `Real.log` and `Real.exp` and so are
stated over `ℝ`. The version here is purely algebraic, which is what makes the semifield
generality possible.

## Main declarations

* `two_le_div_add_div`: `2 ≤ x / y + y / x`.
* `sq_card_le_sum_mul_sum_inv`: the AM-HM inequality.
* `nine_le_sum_mul_sum_inv`: the three-term specialization.
* `nesbitt_inequality`: Nesbitt's inequality, as a corollary.
* `nesbitt_inequality_eq_iff`: the equality case, over a field.
-/

public section

open Finset

variable {ι R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
  {x y z : R}

/-- The two-term AM-HM inequality. This is `two_mul_le_add_sq` divided by `x * y`, and so is
division-free at heart. -/
theorem two_le_div_add_div (hx : 0 < x) (hy : 0 < y) : 2 ≤ x / y + y / x := by
  rw [div_add_div _ _ hy.ne' hx.ne', le_div_iff₀ (by positivity)]
  calc (2 : R) * (y * x) = 2 * x * y := by ring
    _ ≤ x ^ 2 + y ^ 2 := two_mul_le_add_sq x y
    _ = x * x + y * y := by ring

/-- **The AM-HM inequality**: for positive `z`,
`(#s) ^ 2 ≤ (∑ i ∈ s, z i) * (∑ i ∈ s, (z i)⁻¹)`.

This rearranges to the statement that the harmonic mean of `z` is at most its arithmetic mean.
The induction step adjoins an element `a`, producing the cross term
`∑ i ∈ s, (z a / z i + z i / z a)`, each summand of which is at least `2`; that supplies exactly
the `2 * #s` needed by the square of the incremented cardinality. -/
theorem sq_card_le_sum_mul_sum_inv (z : ι → R) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 < z i) →
      (#s : R) ^ 2 ≤ (∑ i ∈ s, z i) * (∑ i ∈ s, (z i)⁻¹) := by
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _; simp
  | cons a s ha ih =>
    intro hz
    have hza : 0 < z a := hz a (by simp)
    have hzs : ∀ i ∈ s, 0 < z i := fun i hi => hz i (by simp [hi])
    have ihs := ih hzs
    rw [Finset.sum_cons, Finset.sum_cons, Finset.card_cons]
    have cross_eq : z a * (∑ i ∈ s, (z i)⁻¹) + (z a)⁻¹ * (∑ i ∈ s, z i)
        = ∑ i ∈ s, (z a / z i + z i / z a) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have cross : 2 * (#s : R) ≤ z a * (∑ i ∈ s, (z i)⁻¹) + (z a)⁻¹ * (∑ i ∈ s, z i) := by
      rw [cross_eq]
      calc 2 * (#s : R) = ∑ _i ∈ s, (2 : R) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ i ∈ s, (z a / z i + z i / z a) :=
            Finset.sum_le_sum fun i hi => two_le_div_add_div hza (hzs i hi)
    push_cast
    calc ((#s : R) + 1) ^ 2 = (#s : R) ^ 2 + 2 * (#s : R) + 1 := by ring
      _ ≤ (∑ i ∈ s, z i) * (∑ i ∈ s, (z i)⁻¹)
            + (z a * (∑ i ∈ s, (z i)⁻¹) + (z a)⁻¹ * (∑ i ∈ s, z i)) + 1 :=
          add_le_add (add_le_add ihs cross) le_rfl
      _ = (z a + ∑ i ∈ s, z i) * ((z a)⁻¹ + ∑ i ∈ s, (z i)⁻¹) := by field_simp; ring

/-- The three-term AM-HM inequality: `9 ≤ (x + y + z) * (x⁻¹ + y⁻¹ + z⁻¹)`. Expanding the
product leaves three ones and three reciprocal pairs, each pair at least `2`. -/
theorem nine_le_sum_mul_sum_inv (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    9 ≤ (x + y + z) * (x⁻¹ + y⁻¹ + z⁻¹) := by
  have key : (x + y + z) * (x⁻¹ + y⁻¹ + z⁻¹)
      = 3 + (x / y + y / x) + (y / z + z / y) + (x / z + z / x) := by field_simp; ring
  rw [key]
  calc (9 : R) = 3 + 2 + 2 + 2 := by norm_num
    _ ≤ 3 + (x / y + y / x) + (y / z + z / y) + (x / z + z / x) :=
        add_le_add (add_le_add (add_le_add le_rfl (two_le_div_add_div hx hy))
          (two_le_div_add_div hy hz)) (two_le_div_add_div hx hz)

/-- **Nesbitt's inequality**, as a corollary of the three-term AM-HM inequality.

Adding `1` to each summand turns the left side into `(a+b+c) * ((b+c)⁻¹ + (c+a)⁻¹ + (a+b)⁻¹)`,
and the three denominators sum to `2 * (a+b+c)`, so AM-HM gives `S + 3 ≥ 9 / 2`. -/
theorem nesbitt_inequality {a b c : R} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have hbc : (0 : R) < b + c := by positivity
  have hca : (0 : R) < c + a := by positivity
  have hab : (0 : R) < a + b := by positivity
  have key := nine_le_sum_mul_sum_inv hbc hca hab
  have expand : a / (b + c) + b / (c + a) + c / (a + b) + 3
      = ((b + c) + ((c + a) + (a + b))) * ((b + c)⁻¹ + (c + a)⁻¹ + (a + b)⁻¹) / 2 := by
    field_simp; ring
  have half : (9 : R) / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) + 3 := by
    rw [expand, le_div_iff₀ (by norm_num)]
    calc (9 : R) / 2 * 2 = 9 := by ring
      _ ≤ ((b + c) + ((c + a) + (a + b))) * ((b + c)⁻¹ + (c + a)⁻¹ + (a + b)⁻¹) := by
          rw [show (b + c) + ((c + a) + (a + b)) = (b + c) + (c + a) + (a + b) by ring]
          exact key
  rw [show (9 : R) / 2 = 3 / 2 + 3 by norm_num] at half
  exact le_of_add_le_add_right half

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c : K}

/-- **The equality case of Nesbitt's inequality**: the sum equals `3 / 2` exactly when
`a = b = c`.

Unlike the inequality itself this is stated over a field rather than a semifield, since the
forward direction certifies the sum-of-squares identity
`(a+b)*(a-b)^2 + (b+c)*(b-c)^2 + (c+a)*(c-a)^2 = 0` and so needs subtraction. -/
theorem nesbitt_inequality_eq_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) = 3 / 2 ↔ a = b ∧ b = c := by
  have hbc : (0 : K) < b + c := by linarith
  have hca : (0 : K) < c + a := by linarith
  have hab : (0 : K) < a + b := by linarith
  constructor
  · intro h
    rw [show a / (b + c) + b / (c + a) + c / (a + b)
          = (a * ((c + a) * (a + b)) + b * ((b + c) * (a + b)) + c * ((b + c) * (c + a)))
            / ((b + c) * ((c + a) * (a + b))) by field_simp] at h
    rw [div_eq_div_iff (by positivity) (by norm_num)] at h
    have key : (a + b) * (a - b) ^ 2 + (b + c) * (b - c) ^ 2 + (c + a) * (c - a) ^ 2 = 0 := by
      linear_combination h
    have t1 : 0 ≤ (a + b) * (a - b) ^ 2 := by positivity
    have t2 : 0 ≤ (b + c) * (b - c) ^ 2 := by positivity
    have t3 : 0 ≤ (c + a) * (c - a) ^ 2 := by positivity
    have e1 : (a + b) * (a - b) ^ 2 = 0 := by linarith
    have e2 : (b + c) * (b - c) ^ 2 = 0 := by linarith
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h' | h'
      · exact absurd h' (by positivity)
      · have := sq_eq_zero_iff.mp h'; linarith
    · rcases mul_eq_zero.mp e2 with h' | h'
      · exact absurd h' (by positivity)
      · have := sq_eq_zero_iff.mp h'; linarith
  · rintro ⟨rfl, rfl⟩
    have h2 : a + a ≠ 0 := by positivity
    field_simp
    norm_num

end Field

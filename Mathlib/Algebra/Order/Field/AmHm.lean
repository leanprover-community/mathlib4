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

for positive `z`, together with its criterion for equality and its two- and three-term
specializations.

## Main statements

* `two_le_div_add_div`: the two-term case, `2 ≤ x / y + y / x`.
* `sq_card_le_sum_mul_sum_inv`: the AM-HM inequality.
* `nine_le_add_add_mul_inv_add_inv_add_inv`: the three-term case.
* `div_add_div_eq_two_iff`: the criterion for equality in the two-term case.
* `sq_card_eq_sum_mul_sum_inv_iff`: the criterion for equality in general.

## Implementation notes

The inequalities hold in a linearly ordered semifield with `ExistsAddOfLE`, so in particular
over `ℚ≥0` and `NNReal`. Semifields have no subtraction, so the usual sum-of-squares argument
is unavailable; the substitute is `two_mul_le_add_sq`, the division-free AM-GM for linearly
ordered commutative semirings. Dividing it by `x * y` gives `two_le_div_add_div`, and summing
that over a `Finset` is the whole content of the general inequality.

The equality criteria are stated over a field rather than a semifield, since the two-term
case amounts to `(x - y) ^ 2 = 0` and so needs subtraction. The general criterion is proved
by symmetrizing: writing the product as `∑ i, ∑ j, z i / z j` and adding it to its own
transpose produces the terms `z i / z j + z j / z i`, each at least `2`, so equality forces
every one of them to equal `2`.

Mathlib's other mean inequalities in `Mathlib/Analysis/MeanInequalities.lean` go through
`Real.log` and `Real.exp` and so are stated over `ℝ`. The version here is purely algebraic,
which is what makes the semifield generality possible.

## References

* <https://en.wikipedia.org/wiki/HM-GM-AM-QM_inequalities>

## Tags

mean inequality, AM-HM, harmonic mean, arithmetic mean
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
theorem nine_le_add_add_mul_inv_add_inv_add_inv (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    9 ≤ (x + y + z) * (x⁻¹ + y⁻¹ + z⁻¹) := by
  have key : (x + y + z) * (x⁻¹ + y⁻¹ + z⁻¹)
      = 3 + (x / y + y / x) + (y / z + z / y) + (x / z + z / x) := by field_simp; ring
  rw [key]
  calc (9 : R) = 3 + 2 + 2 + 2 := by norm_num
    _ ≤ 3 + (x / y + y / x) + (y / z + z / y) + (x / z + z / x) :=
        add_le_add (add_le_add (add_le_add le_rfl (two_le_div_add_div hx hy))
          (two_le_div_add_div hy hz)) (two_le_div_add_div hx hz)

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {x y : K}

/-- Equality holds in the two-term AM-HM inequality exactly when the two terms agree. -/
theorem div_add_div_eq_two_iff (hx : 0 < x) (hy : 0 < y) : x / y + y / x = 2 ↔ x = y := by
  rw [div_add_div _ _ hy.ne' hx.ne', div_eq_iff (by positivity)]
  constructor
  · intro h
    have h2 : (x - y) ^ 2 = 0 := by linear_combination h
    have := sq_eq_zero_iff.mp h2
    linarith
  · rintro rfl
    ring

/-- **The equality criterion for the AM-HM inequality**: equality holds exactly when all the
`z i` coincide.

Symmetrizing the double sum turns the product into terms `z i / z j + z j / z i`, each at
least `2` with total `2 * (#s) ^ 2`; so equality forces every term to equal `2`. -/
theorem sq_card_eq_sum_mul_sum_inv_iff (z : ι → K) (s : Finset ι) (hz : ∀ i ∈ s, 0 < z i) :
    (#s : K) ^ 2 = (∑ i ∈ s, z i) * (∑ i ∈ s, (z i)⁻¹) ↔ ∀ i ∈ s, ∀ j ∈ s, z i = z j := by
  have hprod : (∑ i ∈ s, z i) * (∑ i ∈ s, (z i)⁻¹) = ∑ i ∈ s, ∑ j ∈ s, z i / z j := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => (div_eq_mul_inv _ _).symm
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, (z i / z j + z j / z i)
      = (∑ i ∈ s, ∑ j ∈ s, z i / z j) + (∑ i ∈ s, ∑ j ∈ s, z j / z i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hcomm : (∑ i ∈ s, ∑ j ∈ s, z j / z i) = ∑ i ∈ s, ∑ j ∈ s, z i / z j := Finset.sum_comm
  have hconst : ∑ _i ∈ s, ∑ _j ∈ s, (2 : K) = 2 * (#s : K) ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hterm : ∀ i ∈ s, ∀ j ∈ s, (2 : K) ≤ z i / z j + z j / z i :=
    fun i hi j hj => two_le_div_add_div (hz i hi) (hz j hj)
  constructor
  · intro heq
    have hsum : ∑ i ∈ s, ∑ j ∈ s, (z i / z j + z j / z i) = ∑ _i ∈ s, ∑ _j ∈ s, (2 : K) := by
      rw [hsplit, hcomm, hconst, ← hprod]
      linarith [heq]
    have houter := (Finset.sum_eq_sum_iff_of_le
      (fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj)).mp hsum.symm
    intro i hi j hj
    have hinner := (Finset.sum_eq_sum_iff_of_le (fun j hj => hterm i hi j hj)).mp (houter i hi)
    exact (div_add_div_eq_two_iff (hz i hi) (hz j hj)).mp (hinner j hj).symm
  · intro hall
    have hsum : ∑ i ∈ s, ∑ j ∈ s, (z i / z j + z j / z i) = ∑ _i ∈ s, ∑ _j ∈ s, (2 : K) :=
      Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
        (div_add_div_eq_two_iff (hz i hi) (hz j hj)).mpr (hall i hi j hj)
    rw [hsplit, hcomm, hconst, ← hprod] at hsum
    linarith [hsum]

end Field

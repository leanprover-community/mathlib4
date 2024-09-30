/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric norms

This file contains results on the behavior of norms in ultrametric spaces.

## Main results

* `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`:
  a normed additive group has an ultrametric iff the norm is nonarchimedean

## Implementation details

Some results are proved first about `nnnorm : X → ℝ≥0` because the bottom element
in `NNReal` is 0, so easier to make statements about maxima of empty sets.

## Tags

ultrametric, nonarchimedean
-/
open Metric NNReal

namespace IsUltrametricDist

section Group

variable {S S' ι : Type*} [SeminormedGroup S] [SeminormedGroup S'] [IsUltrametricDist S]

@[to_additive]
lemma norm_mul_le_max (x y : S) :
    ‖x * y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [le_max_iff, dist_eq_norm_div, div_inv_eq_mul, div_one, one_mul] using
    dist_triangle_max x 1 y⁻¹

@[to_additive]
lemma isUltrametricDist_of_forall_norm_mul_le_max_norm
    (h : ∀ x y : S', ‖x * y‖ ≤ max ‖x‖ ‖y‖) : IsUltrametricDist S' where
  dist_triangle_max x y z := by
    simpa only [dist_eq_norm_div, le_max_iff, div_mul_div_cancel] using h (x / y) (y / z)

lemma isUltrametricDist_of_isNonarchimedean_norm {S' : Type*} [SeminormedAddGroup S']
    (h : IsNonarchimedean (norm : S' → ℝ)) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_norm_add_le_max_norm h

@[to_additive]
lemma nnnorm_mul_le_max (x y : S) :
    ‖x * y‖₊ ≤ max ‖x‖₊ ‖y‖₊ :=
  norm_mul_le_max _ _

@[to_additive]
lemma isUltrametricDist_of_forall_nnnorm_mul_le_max_nnnorm
    (h : ∀ x y : S', ‖x * y‖₊ ≤ max ‖x‖₊ ‖y‖₊) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_norm_mul_le_max_norm h

lemma isUltrametricDist_of_isNonarchimedean_nnnorm {S' : Type*} [SeminormedAddGroup S']
    (h : IsNonarchimedean ((↑) ∘ (nnnorm : S' → ℝ≥0))) : IsUltrametricDist S' :=
  isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm h

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive "All triangles are isosceles in an ultrametric normed additive group."]
lemma norm_mul_eq_max_of_norm_ne_norm
    {x y : S} (h : ‖x‖ ≠ ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖ := by
  rw [← div_inv_eq_mul, ← dist_eq_norm_div, dist_eq_max_of_dist_ne_dist _ 1 _ (by simp [h])]
  simp only [dist_one_right, dist_one_left, norm_inv']

@[to_additive]
lemma norm_eq_of_mul_norm_lt_max {x y : S} (h : ‖x * y‖ < max ‖x‖ ‖y‖) :
    ‖x‖ = ‖y‖ :=
  not_ne_iff.mp (h.ne ∘ norm_mul_eq_max_of_norm_ne_norm)

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive "All triangles are isosceles in an ultrametric normed additive group."]
lemma nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm
    {x y : S} (h : ‖x‖₊ ≠ ‖y‖₊) : ‖x * y‖₊ = max ‖x‖₊ ‖y‖₊ := by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using
    norm_mul_eq_max_of_norm_ne_norm (NNReal.coe_injective.ne h)

@[to_additive]
lemma nnnorm_eq_of_mul_nnnorm_lt_max {x y : S} (h : ‖x * y‖₊ < max ‖x‖₊ ‖y‖₊) :
    ‖x‖₊ = ‖y‖₊ :=
  not_ne_iff.mp (h.ne ∘ nnnorm_mul_eq_max_of_nnnorm_ne_nnnorm)

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive "All triangles are isosceles in an ultrametric normed additive group."]
lemma norm_div_eq_max_of_norm_div_ne_norm_div (x y z : S) (h : ‖x / y‖ ≠ ‖y / z‖) :
    ‖x / z‖ = max ‖x / y‖ ‖y / z‖ := by
  simpa only [div_mul_div_cancel] using norm_mul_eq_max_of_norm_ne_norm h

/-- All triangles are isosceles in an ultrametric normed group. -/
@[to_additive "All triangles are isosceles in an ultrametric normed additive group."]
lemma nnnorm_div_eq_max_of_nnnorm_div_ne_nnnorm_div (x y z : S) (h : ‖x / y‖₊ ≠ ‖y / z‖₊) :
    ‖x / z‖₊ = max ‖x / y‖₊ ‖y / z‖₊ := by
  simpa only [← NNReal.coe_inj, NNReal.coe_max] using
    norm_div_eq_max_of_norm_div_ne_norm_div _ _ _ (NNReal.coe_injective.ne h)

@[to_additive]
lemma nnnorm_pow_le (x : S) (n : ℕ) :
    ‖x ^ n‖₊ ≤ ‖x‖₊ := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_add, hn] using nnnorm_mul_le_max (x ^ n) x

@[to_additive]
lemma norm_pow_le (x : S) (n : ℕ) :
    ‖x ^ n‖ ≤ ‖x‖ :=
  nnnorm_pow_le x n

@[to_additive]
lemma nnnorm_zpow_le (x : S) (z : ℤ) :
    ‖x ^ z‖₊ ≤ ‖x‖₊ := by
  cases z <;>
  simpa using nnnorm_pow_le _ _

@[to_additive]
lemma norm_zpow_le (x : S) (z : ℤ) :
    ‖x ^ z‖ ≤ ‖x‖ :=
  nnnorm_zpow_le x z

end Group

section CommGroup

variable {M ι : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- Nonarchimedean norm of a product is less than or equal the norm of any term in the product. -/
@[to_additive "Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum."]
lemma _root_.Finset.nnnorm_prod_le_sup_nnnorm (s : Finset ι) (f : ι → M) :
    ‖∏ i ∈ s, f i‖₊ ≤ s.sup (‖f ·‖₊) := by
  induction s using Finset.cons_induction_on with
  | h₁ => simp
  | @h₂ a s ha IH =>
    simp only [Finset.prod_cons, Finset.sup_cons, le_sup_iff]
    refine (le_total ‖∏ i ∈ s, f i‖ ‖f a‖).imp ?_ ?_ <;> intro h
    · exact (norm_mul_le_max _ _).trans (by simp [h])
    · exact (norm_mul_le_max _ _).trans (by simpa [h] using IH)

/-- Nonarchimedean norm of a product is less than or equal the norm of any term in the product.
This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not.
-/
@[to_additive "Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum.
This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not. "]
lemma _root_.Finset.Nonempty.norm_prod_le_sup'_norm {s : Finset ι} (hs : s.Nonempty) (f : ι → M) :
    ‖∏ i ∈ s, f i‖ ≤ s.sup' hs (‖f ·‖) := by
  simp only [Finset.le_sup'_iff]
  refine Finset.Nonempty.cons_induction ?_ ?_ hs
  · simp
  rintro a s ha _ ⟨b, hb, IH⟩
  simp only [Finset.prod_cons, Finset.mem_cons, exists_eq_or_imp]
  refine (le_total ‖∏ i ∈ s, f i‖ ‖f a‖).imp ?_ ?_ <;> intro h
  · exact (norm_mul_le_max _ _).trans (by simp [h])
  · exact ⟨b, hb, (norm_mul_le_max _ _).trans (by simpa [h] using IH)⟩

/-- Nonarchimedean norm of a product is less than or equal the norm of any term in the product. -/
@[to_additive "Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum."]
lemma _root_.Fintype.nnnorm_prod_le_sup_univ_norm [Fintype ι] (f : ι → M) :
    ‖∏ i, f i‖₊ ≤ Finset.univ.sup (‖f ·‖₊) := by
  simpa using Finset.univ.nnnorm_prod_le_sup_nnnorm f

/-- Nonarchimedean norm of a product is less than or equal the norm of any term in the product. -/
@[to_additive "Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum."]
lemma _root_.Fintype.norm_prod_le_sup'_univ_norm [Nonempty ι] [Fintype ι] (f : ι → M) :
    ‖∏ i, f i‖ ≤ Finset.univ.sup' Finset.univ_nonempty (‖f ·‖) := by
  simpa using Finset.univ_nonempty.norm_prod_le_sup'_norm f

end CommGroup

section DivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]

lemma norm_add_one_le_max_norm_one (x : K) :
    ‖x + 1‖ ≤ max ‖x‖ 1 := by
  simpa using norm_add_le_max x 1

lemma nnnorm_add_one_le_max_nnnorm_one (x : K) :
    ‖x + 1‖₊ ≤ max ‖x‖₊ 1 := by
  simpa using norm_add_le_max x 1

lemma nnnorm_natCast_le_one (n : ℕ) :
    ‖(n : K)‖₊ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn => simpa [hn] using nnnorm_add_one_le_max_nnnorm_one (n : K)

lemma norm_natCast_le_one (n : ℕ) :
    ‖(n : K)‖ ≤ 1 := by
  rw [← Real.toNNReal_le_toNNReal_iff zero_le_one]
  simpa using nnnorm_natCast_le_one n

lemma nnnorm_intCast_le_one (z : ℤ) :
    ‖(z : K)‖₊ ≤ 1 := by
  induction z
  · simpa using nnnorm_natCast_le_one _
  · simpa only [Int.cast_negSucc, Nat.cast_one, nnnorm_neg] using nnnorm_natCast_le_one _

lemma norm_intCast_le_one (z : ℤ) :
    ‖(z : K)‖ ≤ 1 := by
  rw [← Real.toNNReal_le_toNNReal_iff zero_le_one]
  simpa using nnnorm_intCast_le_one z

end DivisionRing

end IsUltrametricDist

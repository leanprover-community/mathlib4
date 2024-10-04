/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, David Loeffler
-/
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric norms

This file contains results on the behavior of norms in ultrametric groups.

## Main results

* `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`:
  a normed additive group has an ultrametric iff the norm is nonarchimedean
* `IsUltrametricDist.nonarchimedeanGroup` and its additive version: instance showing that a
  commutative group with a nonarchimedean seminorm is a nonarchimedean topological group (i.e.
  there is a neighbourhood basis of the identity consisting of open subgroups).

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

section nonarch

variable (S)
/--
In a group with an ultrametric norm, open balls around 1 of positive radius are open subgroups.
-/
@[to_additive "In an additive group with an ultrametric norm, open balls around 0 of
positive radius are open subgroups."]
def ball_openSubgroup {r : ℝ} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.ball (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_ball, dist_eq_norm_div, div_one] at hx hy ⊢
    exact (norm_mul_le_max x y).trans_lt (max_lt hx hy)
  one_mem' := Metric.mem_ball_self hr
  inv_mem' := by simp only [Metric.mem_ball, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := Metric.isOpen_ball

/--
In a group with an ultrametric norm, closed balls around 1 of positive radius are open subgroups.
-/
@[to_additive "In an additive group with an ultrametric norm, closed balls around 0 of positive
radius are open subgroups."]
def closedBall_openSubgroup {r : ℝ} (hr : 0 < r) : OpenSubgroup S where
  carrier := Metric.closedBall (1 : S) r
  mul_mem' {x} {y} hx hy := by
    simp only [Metric.mem_closedBall, dist_eq_norm_div, div_one] at hx hy ⊢
    exact (norm_mul_le_max x y).trans (max_le hx hy)
  one_mem' := Metric.mem_closedBall_self hr.le
  inv_mem' := by simp only [mem_closedBall, dist_one_right, norm_inv', imp_self, implies_true]
  isOpen' := IsUltrametricDist.isOpen_closedBall _ hr.ne'

end nonarch

end Group

section CommGroup

variable {M ι : Type*} [SeminormedCommGroup M] [IsUltrametricDist M]

/-- A commutative group with an ultrametric group seminorm is nonarchimedean (as a topological
group, i.e. every neighborhood of 1 contains an open subgroup). -/
@[to_additive "A commutative additive group with an ultrametric group seminorm is nonarchimedean
(as a topological group, i.e. every neighborhood of 0 contains an open subgroup)."]
instance nonarchimedeanGroup : NonarchimedeanGroup M where
  is_nonarchimedean := by simpa only [Metric.mem_nhds_iff]
    using fun U ⟨ε, hεp, hεU⟩ ↦ ⟨ball_openSubgroup M hεp, hεU⟩

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
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp only [Finset.mem_singleton, Finset.prod_singleton, exists_eq_left, le_refl]
  | cons j t hj _ IH =>
      simp only [Finset.prod_cons, Finset.mem_cons, exists_eq_or_imp]
      refine (le_total ‖∏ i ∈ t, f i‖ ‖f j‖).imp ?_ ?_ <;> intro h
      · exact (norm_mul_le_max _ _).trans (max_eq_left h).le
      · exact ⟨_, IH.choose_spec.left, (norm_mul_le_max _ _).trans <|
          ((max_eq_right h).le.trans IH.choose_spec.right)⟩

/-- Nonarchimedean norm of a product is less than or equal to the largest norm of a term in the
product. -/
@[to_additive "Nonarchimedean norm of a sum is less than or equal to the largest norm of a term in
the sum."]
lemma _root_.Finset.nnnorm_prod_le_sup_nnnorm (s : Finset ι) (f : ι → M) :
    ‖∏ i ∈ s, f i‖₊ ≤ s.sup (‖f ·‖₊) := by
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp only [Finset.prod_empty, nnnorm_one', Finset.sup_empty, bot_eq_zero', le_refl]
  · simpa only [← Finset.sup'_eq_sup hs, Finset.le_sup'_iff, coe_le_coe, coe_nnnorm']
      using hs.norm_prod_le_sup'_norm f

/--
Generalised ultrametric triangle inequality for finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive "Generalised ultrametric triangle inequality for finite sums in additive commutative
groups with an ultrametric norm."]
lemma nnnorm_prod_le_of_forall_le {s : Finset ι} {f : ι → M} {C : ℝ≥0}
    (hC : ∀ i ∈ s, ‖f i‖₊ ≤ C) : ‖∏ i ∈ s, f i‖₊ ≤ C :=
  (s.nnnorm_prod_le_sup_nnnorm f).trans <| Finset.sup_le hC

/--
Generalised ultrametric triangle inequality for nonempty finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive "Generalised ultrametric triangle inequality for nonempty finite sums in additive
commutative groups with an ultrametric norm."]
lemma norm_prod_le_of_forall_le_of_nonempty {s : Finset ι} (hs : s.Nonempty) {f : ι → M} {C : ℝ}
    (hC : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∏ i ∈ s, f i‖ ≤ C :=
  (hs.norm_prod_le_sup'_norm f).trans (Finset.sup'_le hs _ hC)

/--
Generalised ultrametric triangle inequality for finite products in commutative groups with
an ultrametric norm.
-/
@[to_additive "Generalised ultrametric triangle inequality for finite sums in additive commutative
groups with an ultrametric norm."]
lemma norm_prod_le_of_forall_le_of_nonneg {s : Finset ι} {f : ι → M} {C : ℝ}
    (h_nonneg : 0 ≤ C) (hC : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∏ i ∈ s, f i‖ ≤ C := by
  lift C to NNReal using h_nonneg
  exact nnnorm_prod_le_of_forall_le hC

end CommGroup

end IsUltrametricDist

/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.Invertible
import Mathlib.Algebra.IndicatorFunction
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.Tactic.FinCases

#align_import linear_algebra.affine_space.combination from "leanprover-community/mathlib"@"2de9c37fa71dde2f1c6feff19876dd6a7b1519f0"

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weightedVSubOfPoint` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weightedVSub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affineCombination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `Finset`; versions for a
`Fintype` may be obtained using `Finset.univ`, while versions for a
`Finsupp` may be obtained using `Finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/


noncomputable section

open BigOperators Affine

namespace Finset

theorem univ_fin2 : (univ : Finset (Fin 2)) = {0, 1} := by
  ext x
  -- ⊢ x ∈ univ ↔ x ∈ {0, 1}
  fin_cases x <;> simp
  -- ⊢ { val := 0, isLt := (_ : 0 < 2) } ∈ univ ↔ { val := 0, isLt := (_ : 0 < 2) } …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align finset.univ_fin2 Finset.univ_fin2

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AffineSpace V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

/-- A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
def weightedVSubOfPoint (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
  ∑ i in s, (LinearMap.proj i : (ι → k) →ₗ[k] k).smulRight (p i -ᵥ b)
#align finset.weighted_vsub_of_point Finset.weightedVSubOfPoint

@[simp]
theorem weightedVSubOfPoint_apply (w : ι → k) (p : ι → P) (b : P) :
    s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b) := by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_apply Finset.weightedVSubOfPoint_apply

/-- The value of `weightedVSubOfPoint`, where the given points are equal. -/
@[simp (high)]
theorem weightedVSubOfPoint_apply_const (w : ι → k) (p : P) (b : P) :
    s.weightedVSubOfPoint (fun _ => p) b w = (∑ i in s, w i) • (p -ᵥ b) := by
  rw [weightedVSubOfPoint_apply, sum_smul]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_apply_const Finset.weightedVSubOfPoint_apply_const

/-- `weightedVSubOfPoint` gives equal results for two families of weights and two families of
points that are equal on `s`. -/
theorem weightedVSubOfPoint_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) (b : P) :
    s.weightedVSubOfPoint p₁ b w₁ = s.weightedVSubOfPoint p₂ b w₂ := by
  simp_rw [weightedVSubOfPoint_apply]
  -- ⊢ ∑ i in s, w₁ i • (p₁ i -ᵥ b) = ∑ i in s, w₂ i • (p₂ i -ᵥ b)
  refine sum_congr rfl fun i hi => ?_
  -- ⊢ w₁ i • (p₁ i -ᵥ b) = w₂ i • (p₂ i -ᵥ b)
  rw [hw i hi, hp i hi]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_congr Finset.weightedVSubOfPoint_congr

/-- Given a family of points, if we use a member of the family as a base point, the
`weightedVSubOfPoint` does not depend on the value of the weights at this point. -/
theorem weightedVSubOfPoint_eq_of_weights_eq (p : ι → P) (j : ι) (w₁ w₂ : ι → k)
    (hw : ∀ i, i ≠ j → w₁ i = w₂ i) :
    s.weightedVSubOfPoint p (p j) w₁ = s.weightedVSubOfPoint p (p j) w₂ := by
  simp only [Finset.weightedVSubOfPoint_apply]
  -- ⊢ ∑ i in s, w₁ i • (p i -ᵥ p j) = ∑ i in s, w₂ i • (p i -ᵥ p j)
  congr
  -- ⊢ (fun i => w₁ i • (p i -ᵥ p j)) = fun i => w₂ i • (p i -ᵥ p j)
  ext i
  -- ⊢ w₁ i • (p i -ᵥ p j) = w₂ i • (p i -ᵥ p j)
  cases' eq_or_ne i j with h h
  -- ⊢ w₁ i • (p i -ᵥ p j) = w₂ i • (p i -ᵥ p j)
  · simp [h]
    -- 🎉 no goals
  · simp [hw i h]
    -- 🎉 no goals
#align finset.weighted_vsub_of_point_eq_of_weights_eq Finset.weightedVSubOfPoint_eq_of_weights_eq

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
theorem weightedVSubOfPoint_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 0)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w = s.weightedVSubOfPoint p b₂ w := by
  apply eq_of_sub_eq_zero
  -- ⊢ ↑(weightedVSubOfPoint s p b₁) w - ↑(weightedVSubOfPoint s p b₂) w = 0
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← sum_sub_distrib]
  -- ⊢ ∑ x in s, (w x • (p x -ᵥ b₁) - w x • (p x -ᵥ b₂)) = 0
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub, vsub_sub_vsub_cancel_left]
  rw [← sum_smul, h, zero_smul]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_eq_of_sum_eq_zero Finset.weightedVSubOfPoint_eq_of_sum_eq_zero

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
theorem weightedVSubOfPoint_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i in s, w i = 1)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁ = s.weightedVSubOfPoint p b₂ w +ᵥ b₂ := by
  erw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← @vsub_eq_zero_iff_eq V,
    vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ← add_sub_assoc, add_comm, add_sub_assoc, ←
    sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · congr
      · skip
      · ext
        rw [← smul_sub, vsub_sub_vsub_cancel_left]
  rw [← sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_vadd_eq_of_sum_eq_one Finset.weightedVSubOfPoint_vadd_eq_of_sum_eq_one

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp (high)]
theorem weightedVSubOfPoint_erase [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (s.erase i).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  -- ⊢ ∑ i_1 in erase s i, w i_1 • (p i_1 -ᵥ p i) = ∑ i_1 in s, w i_1 • (p i_1 -ᵥ p …
  apply sum_erase
  -- ⊢ w i • (p i -ᵥ p i) = 0
  rw [vsub_self, smul_zero]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_erase Finset.weightedVSubOfPoint_erase

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp (high)]
theorem weightedVSubOfPoint_insert [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (insert i s).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  -- ⊢ ∑ i_1 in insert i s, w i_1 • (p i_1 -ᵥ p i) = ∑ i_1 in s, w i_1 • (p i_1 -ᵥ  …
  apply sum_insert_zero
  -- ⊢ w i • (p i -ᵥ p i) = 0
  rw [vsub_self, smul_zero]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_insert Finset.weightedVSubOfPoint_insert

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weightedVSubOfPoint_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint p b (Set.indicator (↑s₁) w) := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  -- ⊢ ∑ i in s₁, w i • (p i -ᵥ b) = ∑ i in s₂, Set.indicator (↑s₁) w i • (p i -ᵥ b)
  exact
    Set.sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _
#align finset.weighted_vsub_of_point_indicator_subset Finset.weightedVSubOfPoint_indicator_subset

/-- A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`Finset`. -/
theorem weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
    (s₂.map e).weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint (p ∘ e) b (w ∘ e) := by
  simp_rw [weightedVSubOfPoint_apply]
  -- ⊢ ∑ i in map e s₂, w i • (p i -ᵥ b) = ∑ i in s₂, (w ∘ ↑e) i • ((p ∘ ↑e) i -ᵥ b)
  exact Finset.sum_map _ _ _
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_map Finset.weightedVSubOfPoint_map

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two
`weightedVSubOfPoint` expressions. -/
theorem sum_smul_vsub_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ p₂ : ι → P) (b : P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) =
      s.weightedVSubOfPoint p₁ b w - s.weightedVSubOfPoint p₂ b w := by
  simp_rw [weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]
  -- 🎉 no goals
#align finset.sum_smul_vsub_eq_weighted_vsub_of_point_sub Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub

/-- A weighted sum of pairwise subtractions, where the point on the right is constant,
expressed as a subtraction involving a `weightedVSubOfPoint` expression. -/
theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ : ι → P) (p₂ b : P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ i in s, w i) • (p₂ -ᵥ b) :=
  by rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const]
     -- 🎉 no goals
#align finset.sum_smul_vsub_const_eq_weighted_vsub_of_point_sub Finset.sum_smul_vsub_const_eq_weightedVSubOfPoint_sub

/-- A weighted sum of pairwise subtractions, where the point on the left is constant,
expressed as a subtraction involving a `weightedVSubOfPoint` expression. -/
theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι → k) (p₂ : ι → P) (p₁ b : P) :
    (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = (∑ i in s, w i) • (p₁ -ᵥ b) - s.weightedVSubOfPoint p₂ b w :=
  by rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const]
     -- 🎉 no goals
#align finset.sum_smul_const_vsub_eq_sub_weighted_vsub_of_point Finset.sum_smul_const_vsub_eq_sub_weightedVSubOfPoint

/-- A weighted sum may be split into such sums over two subsets. -/
theorem weightedVSubOfPoint_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w + s₂.weightedVSubOfPoint p b w =
      s.weightedVSubOfPoint p b w :=
  by simp_rw [weightedVSubOfPoint_apply, sum_sdiff h]
     -- 🎉 no goals
#align finset.weighted_vsub_of_point_sdiff Finset.weightedVSubOfPoint_sdiff

/-- A weighted sum may be split into a subtraction of such sums over two subsets. -/
theorem weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w - s₂.weightedVSubOfPoint p b (-w) =
      s.weightedVSubOfPoint p b w :=
  by rw [map_neg, sub_neg_eq_add, s.weightedVSubOfPoint_sdiff h]
     -- 🎉 no goals
#align finset.weighted_vsub_of_point_sdiff_sub Finset.weightedVSubOfPoint_sdiff_sub

/-- A weighted sum over `s.subtype pred` equals one over `s.filter pred`. -/
theorem weightedVSubOfPoint_subtype_eq_filter (w : ι → k) (p : ι → P) (b : P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSubOfPoint (fun i => p i) b fun i => w i) =
      (s.filter pred).weightedVSubOfPoint p b w :=
  by rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← sum_subtype_eq_sum_filter]
     -- 🎉 no goals
#align finset.weighted_vsub_of_point_subtype_eq_filter Finset.weightedVSubOfPoint_subtype_eq_filter

/-- A weighted sum over `s.filter pred` equals one over `s` if all the weights at indices in `s`
not satisfying `pred` are zero. -/
theorem weightedVSubOfPoint_filter_of_ne (w : ι → k) (p : ι → P) (b : P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    (s.filter pred).weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, sum_filter_of_ne]
  -- ⊢ ∀ (x : ι), x ∈ s → w x • (p x -ᵥ b) ≠ 0 → pred x
  intro i hi hne
  -- ⊢ pred i
  refine' h i hi _
  -- ⊢ w i ≠ 0
  intro hw
  -- ⊢ False
  simp [hw] at hne
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_filter_of_ne Finset.weightedVSubOfPoint_filter_of_ne

/-- A constant multiplier of the weights in `weightedVSubOfPoint` may be moved outside the
sum. -/
theorem weightedVSubOfPoint_const_smul (w : ι → k) (p : ι → P) (b : P) (c : k) :
    s.weightedVSubOfPoint p b (c • w) = c • s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]
  -- 🎉 no goals
#align finset.weighted_vsub_of_point_const_smul Finset.weightedVSubOfPoint_const_smul

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weightedVSub (p : ι → P) : (ι → k) →ₗ[k] V :=
  s.weightedVSubOfPoint p (Classical.choice S.Nonempty)
#align finset.weighted_vsub Finset.weightedVSub

/-- Applying `weightedVSub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weightedVSub` would involve selecting a preferred base point with
`weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` and then
using `weightedVSubOfPoint_apply`. -/
theorem weightedVSub_apply (w : ι → k) (p : ι → P) :
    s.weightedVSub p w = ∑ i in s, w i • (p i -ᵥ Classical.choice S.Nonempty) := by
  simp [weightedVSub, LinearMap.sum_apply]
  -- 🎉 no goals
#align finset.weighted_vsub_apply Finset.weightedVSub_apply

/-- `weightedVSub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w :=
  s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _
#align finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero

/-- The value of `weightedVSub`, where the given points are equal and the sum of the weights
is 0. -/
@[simp]
theorem weightedVSub_apply_const (w : ι → k) (p : P) (h : ∑ i in s, w i = 0) :
    s.weightedVSub (fun _ => p) w = 0 := by
  rw [weightedVSub, weightedVSubOfPoint_apply_const, h, zero_smul]
  -- 🎉 no goals
#align finset.weighted_vsub_apply_const Finset.weightedVSub_apply_const

/-- The `weightedVSub` for an empty set is 0. -/
@[simp]
theorem weightedVSub_empty (w : ι → k) (p : ι → P) : (∅ : Finset ι).weightedVSub p w = (0 : V) := by
  simp [weightedVSub_apply]
  -- 🎉 no goals
#align finset.weighted_vsub_empty Finset.weightedVSub_empty

/-- `weightedVSub` gives equal results for two families of weights and two families of points
that are equal on `s`. -/
theorem weightedVSub_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.weightedVSub p₁ w₁ = s.weightedVSub p₂ w₂ :=
  s.weightedVSubOfPoint_congr hw hp _
#align finset.weighted_vsub_congr Finset.weightedVSub_congr

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weightedVSub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
    s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (↑s₁) w) :=
  weightedVSubOfPoint_indicator_subset _ _ _ h
#align finset.weighted_vsub_indicator_subset Finset.weightedVSub_indicator_subset

/-- A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `Finset`. -/
theorem weightedVSub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e) :=
  s₂.weightedVSubOfPoint_map _ _ _ _
#align finset.weighted_vsub_map Finset.weightedVSub_map

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two `weightedVSub`
expressions. -/
theorem sum_smul_vsub_eq_weightedVSub_sub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w :=
  s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _
#align finset.sum_smul_vsub_eq_weighted_vsub_sub Finset.sum_smul_vsub_eq_weightedVSub_sub

/-- A weighted sum of pairwise subtractions, where the point on the right is constant and the
sum of the weights is 0. -/
theorem sum_smul_vsub_const_eq_weightedVSub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i in s, w i = 0) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSub p₁ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub, s.weightedVSub_apply_const _ _ h, sub_zero]
  -- 🎉 no goals
#align finset.sum_smul_vsub_const_eq_weighted_vsub Finset.sum_smul_vsub_const_eq_weightedVSub

/-- A weighted sum of pairwise subtractions, where the point on the left is constant and the
sum of the weights is 0. -/
theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i in s, w i = 0) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub, s.weightedVSub_apply_const _ _ h, zero_sub]
  -- 🎉 no goals
#align finset.sum_smul_const_vsub_eq_neg_weighted_vsub Finset.sum_smul_const_vsub_eq_neg_weightedVSub

/-- A weighted sum may be split into such sums over two subsets. -/
theorem weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k) (p : ι → P) :
    (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff h _ _ _
#align finset.weighted_vsub_sdiff Finset.weightedVSub_sdiff

/-- A weighted sum may be split into a subtraction of such sums over two subsets. -/
theorem weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff_sub h _ _ _
#align finset.weighted_vsub_sdiff_sub Finset.weightedVSub_sdiff_sub

/-- A weighted sum over `s.subtype pred` equals one over `s.filter pred`. -/
theorem weightedVSub_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSub (fun i => p i) fun i => w i) =
      (s.filter pred).weightedVSub p w :=
  s.weightedVSubOfPoint_subtype_eq_filter _ _ _ _
#align finset.weighted_vsub_subtype_eq_filter Finset.weightedVSub_subtype_eq_filter

/-- A weighted sum over `s.filter pred` equals one over `s` if all the weights at indices in `s`
not satisfying `pred` are zero. -/
theorem weightedVSub_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop} [DecidablePred pred]
    (h : ∀ i ∈ s, w i ≠ 0 → pred i) : (s.filter pred).weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_filter_of_ne _ _ _ h
#align finset.weighted_vsub_filter_of_ne Finset.weightedVSub_filter_of_ne

/-- A constant multiplier of the weights in `weightedVSub_of` may be moved outside the sum. -/
theorem weightedVSub_const_smul (w : ι → k) (p : ι → P) (c : k) :
    s.weightedVSub p (c • w) = c • s.weightedVSub p w :=
  s.weightedVSubOfPoint_const_smul _ _ _ _
#align finset.weighted_vsub_const_smul Finset.weightedVSub_const_smul

instance : AffineSpace (ι → k) (ι → k) := Pi.instAddTorsor

variable (k)

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it. -/
def affineCombination (p : ι → P) : (ι → k) →ᵃ[k] P
    where
  toFun w := s.weightedVSubOfPoint p (Classical.choice S.Nonempty) w +ᵥ Classical.choice S.Nonempty
  linear := s.weightedVSub p
  map_vadd' w₁ w₂ := by simp_rw [vadd_vadd, weightedVSub, vadd_eq_add, LinearMap.map_add]
                        -- 🎉 no goals
#align finset.affine_combination Finset.affineCombination

/-- The linear map corresponding to `affineCombination` is
`weightedVSub`. -/
@[simp]
theorem affineCombination_linear (p : ι → P) :
    (s.affineCombination k p).linear = s.weightedVSub p :=
  rfl
#align finset.affine_combination_linear Finset.affineCombination_linear

variable {k}

/-- Applying `affineCombination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affineCombination` would involve selecting a preferred base
point with
`affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one` and
then using `weightedVSubOfPoint_apply`. -/
theorem affineCombination_apply (w : ι → k) (p : ι → P) :
    (s.affineCombination k p) w =
      s.weightedVSubOfPoint p (Classical.choice S.Nonempty) w +ᵥ Classical.choice S.Nonempty :=
  rfl
#align finset.affine_combination_apply Finset.affineCombination_apply

/-- The value of `affineCombination`, where the given points are equal. -/
@[simp]
theorem affineCombination_apply_const (w : ι → k) (p : P) (h : ∑ i in s, w i = 1) :
    s.affineCombination k (fun _ => p) w = p := by
  rw [affineCombination_apply, s.weightedVSubOfPoint_apply_const, h, one_smul, vsub_vadd]
  -- 🎉 no goals
#align finset.affine_combination_apply_const Finset.affineCombination_apply_const

/-- `affineCombination` gives equal results for two families of weights and two families of
points that are equal on `s`. -/
theorem affineCombination_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.affineCombination k p₁ w₁ = s.affineCombination k p₂ w₂ := by
  simp_rw [affineCombination_apply, s.weightedVSubOfPoint_congr hw hp]
  -- 🎉 no goals
#align finset.affine_combination_congr Finset.affineCombination_congr

/-- `affineCombination` gives the sum with any base point, when the
sum of the weights is 1. -/
theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i in s, w i = 1) (b : P) :
    s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b :=
  s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w p h _ _
#align finset.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one

/-- Adding a `weightedVSub` to an `affineCombination`. -/
theorem weightedVSub_vadd_affineCombination (w₁ w₂ : ι → k) (p : ι → P) :
    s.weightedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂) := by
  rw [← vadd_eq_add, AffineMap.map_vadd, affineCombination_linear]
  -- 🎉 no goals
#align finset.weighted_vsub_vadd_affine_combination Finset.weightedVSub_vadd_affineCombination

/-- Subtracting two `affineCombination`s. -/
theorem affineCombination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
    s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weightedVSub p (w₁ - w₂) := by
  rw [← AffineMap.linearMap_vsub, affineCombination_linear, vsub_eq_sub]
  -- 🎉 no goals
#align finset.affine_combination_vsub Finset.affineCombination_vsub

theorem attach_affineCombination_of_injective [DecidableEq P] (s : Finset P) (w : P → k) (f : s → P)
    (hf : Function.Injective f) :
    s.attach.affineCombination k f (w ∘ f) = (image f univ).affineCombination k id w := by
  simp only [affineCombination, weightedVSubOfPoint_apply, id.def, vadd_right_cancel_iff,
    Function.comp_apply, AffineMap.coe_mk]
  let g₁ : s → V := fun i => w (f i) • (f i -ᵥ Classical.choice S.Nonempty)
  -- ⊢ ∑ x in attach s, w (f x) • (f x -ᵥ Classical.choice (_ : Nonempty P)) = ∑ x  …
  let g₂ : P → V := fun i => w i • (i -ᵥ Classical.choice S.Nonempty)
  -- ⊢ ∑ x in attach s, w (f x) • (f x -ᵥ Classical.choice (_ : Nonempty P)) = ∑ x  …
  change univ.sum g₁ = (image f univ).sum g₂
  -- ⊢ Finset.sum univ g₁ = Finset.sum (image f univ) g₂
  have hgf : g₁ = g₂ ∘ f := by
    ext
    simp
  rw [hgf, sum_image]
  -- ⊢ Finset.sum univ (g₂ ∘ f) = ∑ x : { x // x ∈ s }, w (f x) • (f x -ᵥ Classical …
  simp only [Function.comp_apply]
  -- ⊢ ∀ (x : { x // x ∈ s }), x ∈ univ → ∀ (y : { x // x ∈ s }), y ∈ univ → f x =  …
  exact fun _ _ _ _ hxy => hf hxy
  -- 🎉 no goals
#align finset.attach_affine_combination_of_injective Finset.attach_affineCombination_of_injective

theorem attach_affineCombination_coe (s : Finset P) (w : P → k) :
    s.attach.affineCombination k ((↑) : s → P) (w ∘ (↑)) = s.affineCombination k id w := by
  classical rw [attach_affineCombination_of_injective s w ((↑) : s → P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]
#align finset.attach_affine_combination_coe Finset.attach_affineCombination_coe

/-- Viewing a module as an affine space modelled on itself, a `weightedVSub` is just a linear
combination. -/
@[simp]
theorem weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι → k} {p : ι → V}
    (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i in s, w i • p i := by
  simp [s.weightedVSub_apply, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]
  -- 🎉 no goals
#align finset.weighted_vsub_eq_linear_combination Finset.weightedVSub_eq_linear_combination

/-- Viewing a module as an affine space modelled on itself, affine combinations are just linear
combinations. -/
@[simp]
theorem affineCombination_eq_linear_combination (s : Finset ι) (p : ι → V) (w : ι → k)
    (hw : ∑ i in s, w i = 1) : s.affineCombination k p w = ∑ i in s, w i • p i := by
  simp [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw 0]
  -- 🎉 no goals
#align finset.affine_combination_eq_linear_combination Finset.affineCombination_eq_linear_combination

/-- An `affineCombination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
@[simp]
theorem affineCombination_of_eq_one_of_eq_zero (w : ι → k) (p : ι → P) {i : ι} (his : i ∈ s)
    (hwi : w i = 1) (hw0 : ∀ i2 ∈ s, i2 ≠ i → w i2 = 0) : s.affineCombination k p w = p i := by
  have h1 : ∑ i in s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  -- ⊢ ↑(affineCombination k s p) w = p i
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i),
    weightedVSubOfPoint_apply]
  convert zero_vadd V (p i)
  -- ⊢ ∑ i_1 in s, w i_1 • (p i_1 -ᵥ p i) = 0
  refine sum_eq_zero ?_
  -- ⊢ ∀ (x : ι), x ∈ s → w x • (p x -ᵥ p i) = 0
  intro i2 hi2
  -- ⊢ w i2 • (p i2 -ᵥ p i) = 0
  by_cases h : i2 = i
  -- ⊢ w i2 • (p i2 -ᵥ p i) = 0
  · simp [h]
    -- 🎉 no goals
  · simp [hw0 i2 hi2 h]
    -- 🎉 no goals
#align finset.affine_combination_of_eq_one_of_eq_zero Finset.affineCombination_of_eq_one_of_eq_zero

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem affineCombination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.affineCombination k p w = s₂.affineCombination k p (Set.indicator (↑s₁) w) := by
  rw [affineCombination_apply, affineCombination_apply,
    weightedVSubOfPoint_indicator_subset _ _ _ h]
#align finset.affine_combination_indicator_subset Finset.affineCombination_indicator_subset

/-- An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`Finset`. -/
theorem affineCombination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).affineCombination k p w = s₂.affineCombination k (p ∘ e) (w ∘ e) := by
  simp_rw [affineCombination_apply, weightedVSubOfPoint_map]
  -- 🎉 no goals
#align finset.affine_combination_map Finset.affineCombination_map

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two `affineCombination`
expressions. -/
theorem sum_smul_vsub_eq_affineCombination_vsub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i in s, w i • (p₁ i -ᵥ p₂ i)) =
      s.affineCombination k p₁ w -ᵥ s.affineCombination k p₂ w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  -- ⊢ ∑ i in s, w i • (p₁ i -ᵥ p₂ i) = ↑(weightedVSubOfPoint s p₁ (Classical.choic …
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _
  -- 🎉 no goals
#align finset.sum_smul_vsub_eq_affine_combination_vsub Finset.sum_smul_vsub_eq_affineCombination_vsub

/-- A weighted sum of pairwise subtractions, where the point on the right is constant and the
sum of the weights is 1. -/
theorem sum_smul_vsub_const_eq_affineCombination_vsub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i in s, w i = 1) : (∑ i in s, w i • (p₁ i -ᵥ p₂)) = s.affineCombination k p₁ w -ᵥ p₂ :=
  by rw [sum_smul_vsub_eq_affineCombination_vsub, affineCombination_apply_const _ _ _ h]
     -- 🎉 no goals
#align finset.sum_smul_vsub_const_eq_affine_combination_vsub Finset.sum_smul_vsub_const_eq_affineCombination_vsub

/-- A weighted sum of pairwise subtractions, where the point on the left is constant and the
sum of the weights is 1. -/
theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i in s, w i = 1) : (∑ i in s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w :=
  by rw [sum_smul_vsub_eq_affineCombination_vsub, affineCombination_apply_const _ _ _ h]
     -- 🎉 no goals
#align finset.sum_smul_const_vsub_eq_vsub_affine_combination Finset.sum_smul_const_vsub_eq_vsub_affineCombination

/-- A weighted sum may be split into a subtraction of affine combinations over two subsets. -/
theorem affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) :
    (s \ s₂).affineCombination k p w -ᵥ s₂.affineCombination k p (-w) = s.weightedVSub p w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  -- ⊢ ↑(weightedVSubOfPoint (s \ s₂) p (Classical.choice (_ : Nonempty P))) w - ↑( …
  exact s.weightedVSub_sdiff_sub h _ _
  -- 🎉 no goals
#align finset.affine_combination_sdiff_sub Finset.affineCombination_sdiff_sub

/-- If a weighted sum is zero and one of the weights is `-1`, the corresponding point is
the affine combination of the other points with the given weights. -/
theorem affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι → k} {p : ι → P}
    (hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidablePred (· ≠ i)] (his : i ∈ s)
    (hwi : w i = -1) : (s.filter (· ≠ i)).affineCombination k p w = p i := by
  classical
    rw [← @vsub_eq_zero_iff_eq V, ← hw,
      ← s.affineCombination_sdiff_sub (singleton_subset_iff.2 his), sdiff_singleton_eq_erase,
      ← filter_ne']
    congr
    refine' (affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) _ _).symm
    · simp [hwi]
    · simp
#align finset.affine_combination_eq_of_weighted_vsub_eq_zero_of_eq_neg_one Finset.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one

/-- An affine combination over `s.subtype pred` equals one over `s.filter pred`. -/
theorem affineCombination_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).affineCombination k (fun i => p i) fun i => w i) =
      (s.filter pred).affineCombination k p w := by
  rw [affineCombination_apply, affineCombination_apply, weightedVSubOfPoint_subtype_eq_filter]
  -- 🎉 no goals
#align finset.affine_combination_subtype_eq_filter Finset.affineCombination_subtype_eq_filter

/-- An affine combination over `s.filter pred` equals one over `s` if all the weights at indices
in `s` not satisfying `pred` are zero. -/
theorem affineCombination_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    (s.filter pred).affineCombination k p w = s.affineCombination k p w := by
  rw [affineCombination_apply, affineCombination_apply,
    s.weightedVSubOfPoint_filter_of_ne _ _ _ h]
#align finset.affine_combination_filter_of_ne Finset.affineCombination_filter_of_ne

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weightedVSubOfPoint` using a `Finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weightedVSubOfPoint` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k} {s : Set ι}
    {p : ι → P} {b : P} :
    (∃ (fs : Finset ι) (_ : ↑fs ⊆ s) (w : ι → k) (_ : ∑ i in fs, w i = x),
        v = fs.weightedVSubOfPoint p b w) ↔
      ∃ (fs : Finset s) (w : s → k) (_ : ∑ i in fs, w i = x),
        v = fs.weightedVSubOfPoint (fun i : s => p i) b w := by
  classical
    simp_rw [weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype s, fun i => w i, sum_subtype_of_mem _ hfs, (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine'
          ⟨fs.map (Function.Embedding.subtype _), map_subtype_subset _, fun i =>
            if h : i ∈ s then w ⟨i, h⟩ else 0, _, _⟩ <;>
        simp
#align finset.eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype Finset.eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

variable (k)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weightedVSub` using
a `Finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weightedVSub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weightedVSub_subset_iff_eq_weightedVSub_subtype {v : V} {s : Set ι} {p : ι → P} :
    (∃ (fs : Finset ι) (_ : ↑fs ⊆ s) (w : ι → k) (_ : ∑ i in fs, w i = 0),
        v = fs.weightedVSub p w) ↔
      ∃ (fs : Finset s) (w : s → k) (_ : ∑ i in fs, w i = 0),
        v = fs.weightedVSub (fun i : s => p i) w :=
  eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype
#align finset.eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype Finset.eq_weightedVSub_subset_iff_eq_weightedVSub_subtype

variable (V)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affineCombination` using a `Finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affineCombination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset. -/
theorem eq_affineCombination_subset_iff_eq_affineCombination_subtype {p0 : P} {s : Set ι}
    {p : ι → P} :
    (∃ (fs : Finset ι) (_ : ↑fs ⊆ s) (w : ι → k) (_ : ∑ i in fs, w i = 1),
        p0 = fs.affineCombination k p w) ↔
      ∃ (fs : Finset s) (w : s → k) (_ : ∑ i in fs, w i = 1),
        p0 = fs.affineCombination k (fun i : s => p i) w := by
  simp_rw [affineCombination_apply, eq_vadd_iff_vsub_eq]
  -- ⊢ (∃ fs h w h, p0 -ᵥ Classical.choice (_ : Nonempty P) = ↑(weightedVSubOfPoint …
  exact eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype
  -- 🎉 no goals
#align finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype

variable {k V}

/-- Affine maps commute with affine combinations. -/
theorem map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
    (p : ι → P) (w : ι → k) (hw : s.sum w = 1) (f : P →ᵃ[k] P₂) :
    f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w := by
  have b := Classical.choice (inferInstance : AffineSpace V P).Nonempty
  -- ⊢ ↑f (↑(affineCombination k s p) w) = ↑(affineCombination k s (↑f ∘ p)) w
  have b₂ := Classical.choice (inferInstance : AffineSpace V₂ P₂).Nonempty
  -- ⊢ ↑f (↑(affineCombination k s p) w) = ↑(affineCombination k s (↑f ∘ p)) w
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw b,
    s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w (f ∘ p) hw b₂, ←
    s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w (f ∘ p) hw (f b) b₂]
  simp only [weightedVSubOfPoint_apply, RingHom.id_apply, AffineMap.map_vadd,
    LinearMap.map_smulₛₗ, AffineMap.linearMap_vsub, LinearMap.map_sum, Function.comp_apply]
#align finset.map_affine_combination Finset.map_affineCombination

variable (k)

/-- Weights for expressing a single point as an affine combination. -/
def affineCombinationSingleWeights [DecidableEq ι] (i : ι) : ι → k :=
  Function.update (Function.const ι 0) i 1
#align finset.affine_combination_single_weights Finset.affineCombinationSingleWeights

@[simp]
theorem affineCombinationSingleWeights_apply_self [DecidableEq ι] (i : ι) :
    affineCombinationSingleWeights k i i = 1 := by simp [affineCombinationSingleWeights]
                                                   -- 🎉 no goals
#align finset.affine_combination_single_weights_apply_self Finset.affineCombinationSingleWeights_apply_self

@[simp]
theorem affineCombinationSingleWeights_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    affineCombinationSingleWeights k i j = 0 := by simp [affineCombinationSingleWeights, h]
                                                   -- 🎉 no goals
#align finset.affine_combination_single_weights_apply_of_ne Finset.affineCombinationSingleWeights_apply_of_ne

@[simp]
theorem sum_affineCombinationSingleWeights [DecidableEq ι] {i : ι} (h : i ∈ s) :
    ∑ j in s, affineCombinationSingleWeights k i j = 1 := by
  rw [← affineCombinationSingleWeights_apply_self k i]
  -- ⊢ ∑ j in s, affineCombinationSingleWeights k i j = affineCombinationSingleWeig …
  exact sum_eq_single_of_mem i h fun j _ hj => affineCombinationSingleWeights_apply_of_ne k hj
  -- 🎉 no goals
#align finset.sum_affine_combination_single_weights Finset.sum_affineCombinationSingleWeights

/-- Weights for expressing the subtraction of two points as a `weightedVSub`. -/
def weightedVSubVSubWeights [DecidableEq ι] (i j : ι) : ι → k :=
  affineCombinationSingleWeights k i - affineCombinationSingleWeights k j
#align finset.weighted_vsub_vsub_weights Finset.weightedVSubVSubWeights

@[simp]
theorem weightedVSubVSubWeights_self [DecidableEq ι] (i : ι) : weightedVSubVSubWeights k i i = 0 :=
  by simp [weightedVSubVSubWeights]
     -- 🎉 no goals
#align finset.weighted_vsub_vsub_weights_self Finset.weightedVSubVSubWeights_self

@[simp]
theorem weightedVSubVSubWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    weightedVSubVSubWeights k i j i = 1 := by simp [weightedVSubVSubWeights, h]
                                              -- 🎉 no goals
#align finset.weighted_vsub_vsub_weights_apply_left Finset.weightedVSubVSubWeights_apply_left

@[simp]
theorem weightedVSubVSubWeights_apply_right [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    weightedVSubVSubWeights k i j j = -1 := by simp [weightedVSubVSubWeights, h.symm]
                                               -- 🎉 no goals
#align finset.weighted_vsub_vsub_weights_apply_right Finset.weightedVSubVSubWeights_apply_right

@[simp]
theorem weightedVSubVSubWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i) (hj : t ≠ j) :
    weightedVSubVSubWeights k i j t = 0 := by simp [weightedVSubVSubWeights, hi, hj]
                                              -- 🎉 no goals
#align finset.weighted_vsub_vsub_weights_apply_of_ne Finset.weightedVSubVSubWeights_apply_of_ne

@[simp]
theorem sum_weightedVSubVSubWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    ∑ t in s, weightedVSubVSubWeights k i j t = 0 := by
  simp_rw [weightedVSubVSubWeights, Pi.sub_apply, sum_sub_distrib]
  -- ⊢ ∑ x in s, affineCombinationSingleWeights k i x - ∑ x in s, affineCombination …
  simp [hi, hj]
  -- 🎉 no goals
#align finset.sum_weighted_vsub_vsub_weights Finset.sum_weightedVSubVSubWeights

variable {k}

/-- Weights for expressing `lineMap` as an affine combination. -/
def affineCombinationLineMapWeights [DecidableEq ι] (i j : ι) (c : k) : ι → k :=
  c • weightedVSubVSubWeights k j i + affineCombinationSingleWeights k i
#align finset.affine_combination_line_map_weights Finset.affineCombinationLineMapWeights

@[simp]
theorem affineCombinationLineMapWeights_self [DecidableEq ι] (i : ι) (c : k) :
    affineCombinationLineMapWeights i i c = affineCombinationSingleWeights k i := by
  simp [affineCombinationLineMapWeights]
  -- 🎉 no goals
#align finset.affine_combination_line_map_weights_self Finset.affineCombinationLineMapWeights_self

@[simp]
theorem affineCombinationLineMapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    affineCombinationLineMapWeights i j c i = 1 - c := by
  simp [affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]
  -- 🎉 no goals
#align finset.affine_combination_line_map_weights_apply_left Finset.affineCombinationLineMapWeights_apply_left

@[simp]
theorem affineCombinationLineMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    affineCombinationLineMapWeights i j c j = c := by
  simp [affineCombinationLineMapWeights, h.symm]
  -- 🎉 no goals
#align finset.affine_combination_line_map_weights_apply_right Finset.affineCombinationLineMapWeights_apply_right

@[simp]
theorem affineCombinationLineMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i)
    (hj : t ≠ j) (c : k) : affineCombinationLineMapWeights i j c t = 0 := by
  simp [affineCombinationLineMapWeights, hi, hj]
  -- 🎉 no goals
#align finset.affine_combination_line_map_weights_apply_of_ne Finset.affineCombinationLineMapWeights_apply_of_ne

@[simp]
theorem sum_affineCombinationLineMapWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (c : k) : ∑ t in s, affineCombinationLineMapWeights i j c t = 1 := by
  simp_rw [affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  -- ⊢ ∑ x in s, (c • weightedVSubVSubWeights k j i) x + ∑ x in s, affineCombinatio …
  simp [hi, hj, ← mul_sum]
  -- 🎉 no goals
#align finset.sum_affine_combination_line_map_weights Finset.sum_affineCombinationLineMapWeights

variable (k)

/-- An affine combination with `affineCombinationSingleWeights` gives the specified point. -/
@[simp]
theorem affineCombination_affineCombinationSingleWeights [DecidableEq ι] (p : ι → P) {i : ι}
    (hi : i ∈ s) : s.affineCombination k p (affineCombinationSingleWeights k i) = p i := by
  refine' s.affineCombination_of_eq_one_of_eq_zero _ _ hi (by simp) _
  -- ⊢ ∀ (i2 : ι), i2 ∈ s → i2 ≠ i → affineCombinationSingleWeights k i i2 = 0
  rintro j - hj
  -- ⊢ affineCombinationSingleWeights k i j = 0
  simp [hj]
  -- 🎉 no goals
#align finset.affine_combination_affine_combination_single_weights Finset.affineCombination_affineCombinationSingleWeights

/-- A weighted subtraction with `weightedVSubVSubWeights` gives the result of subtracting the
specified points. -/
@[simp]
theorem weightedVSub_weightedVSubVSubWeights [DecidableEq ι] (p : ι → P) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) : s.weightedVSub p (weightedVSubVSubWeights k i j) = p i -ᵥ p j := by
  rw [weightedVSubVSubWeights, ← affineCombination_vsub,
    s.affineCombination_affineCombinationSingleWeights k p hi,
    s.affineCombination_affineCombinationSingleWeights k p hj]
#align finset.weighted_vsub_weighted_vsub_vsub_weights Finset.weightedVSub_weightedVSubVSubWeights

variable {k}

/-- An affine combination with `affineCombinationLineMapWeights` gives the result of
`line_map`. -/
@[simp]
theorem affineCombination_affineCombinationLineMapWeights [DecidableEq ι] (p : ι → P) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (c : k) :
    s.affineCombination k p (affineCombinationLineMapWeights i j c) =
      AffineMap.lineMap (p i) (p j) c := by
  rw [affineCombinationLineMapWeights, ← weightedVSub_vadd_affineCombination,
    weightedVSub_const_smul, s.affineCombination_affineCombinationSingleWeights k p hi,
    s.weightedVSub_weightedVSubVSubWeights k p hj hi, AffineMap.lineMap_apply]
#align finset.affine_combination_affine_combination_line_map_weights Finset.affineCombination_affineCombinationLineMapWeights

end Finset

namespace Finset

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AffineSpace V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

/-- The weights for the centroid of some points. -/
def centroidWeights : ι → k :=
  Function.const ι (card s : k)⁻¹
#align finset.centroid_weights Finset.centroidWeights

/-- `centroidWeights` at any point. -/
@[simp]
theorem centroidWeights_apply (i : ι) : s.centroidWeights k i = (card s : k)⁻¹ :=
  rfl
#align finset.centroid_weights_apply Finset.centroidWeights_apply

/-- `centroidWeights` equals a constant function. -/
theorem centroidWeights_eq_const : s.centroidWeights k = Function.const ι (card s : k)⁻¹ :=
  rfl
#align finset.centroid_weights_eq_const Finset.centroidWeights_eq_const

variable {k}

/-- The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero. -/
theorem sum_centroidWeights_eq_one_of_cast_card_ne_zero (h : (card s : k) ≠ 0) :
    ∑ i in s, s.centroidWeights k i = 1 := by simp [h]
                                              -- 🎉 no goals
#align finset.sum_centroid_weights_eq_one_of_cast_card_ne_zero Finset.sum_centroidWeights_eq_one_of_cast_card_ne_zero

variable (k)

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero. -/
theorem sum_centroidWeights_eq_one_of_card_ne_zero [CharZero k] (h : card s ≠ 0) :
    ∑ i in s, s.centroidWeights k i = 1 := by
  -- Porting note: `simp` cannot find `mul_inv_cancel` and does not use `norm_cast`
  simp only [centroidWeights_apply, sum_const, nsmul_eq_mul, ne_eq, Nat.cast_eq_zero, card_eq_zero]
  -- ⊢ ↑(card s) * (↑(card s))⁻¹ = 1
  refine mul_inv_cancel ?_
  -- ⊢ ↑(card s) ≠ 0
  norm_cast
  -- 🎉 no goals
#align finset.sum_centroid_weights_eq_one_of_card_ne_zero Finset.sum_centroidWeights_eq_one_of_card_ne_zero

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty. -/
theorem sum_centroidWeights_eq_one_of_nonempty [CharZero k] (h : s.Nonempty) :
    ∑ i in s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))
#align finset.sum_centroid_weights_eq_one_of_nonempty Finset.sum_centroidWeights_eq_one_of_nonempty

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`. -/
theorem sum_centroidWeights_eq_one_of_card_eq_add_one [CharZero k] {n : ℕ} (h : card s = n + 1) :
    ∑ i in s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)
#align finset.sum_centroid_weights_eq_one_of_card_eq_add_one Finset.sum_centroidWeights_eq_one_of_card_eq_add_one

/-- The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero. -/
def centroid (p : ι → P) : P :=
  s.affineCombination k p (s.centroidWeights k)
#align finset.centroid Finset.centroid

/-- The definition of the centroid. -/
theorem centroid_def (p : ι → P) : s.centroid k p = s.affineCombination k p (s.centroidWeights k) :=
  rfl
#align finset.centroid_def Finset.centroid_def

theorem centroid_univ (s : Finset P) : univ.centroid k ((↑) : s → P) = s.centroid k id := by
  rw [centroid, centroid, ← s.attach_affineCombination_coe]
  -- ⊢ ↑(affineCombination k univ Subtype.val) (centroidWeights k univ) = ↑(affineC …
  congr
  -- ⊢ centroidWeights k univ = centroidWeights k s ∘ Subtype.val
  ext
  -- ⊢ centroidWeights k univ x✝ = (centroidWeights k s ∘ Subtype.val) x✝
  simp
  -- 🎉 no goals
#align finset.centroid_univ Finset.centroid_univ

/-- The centroid of a single point. -/
@[simp]
theorem centroid_singleton (p : ι → P) (i : ι) : ({i} : Finset ι).centroid k p = p i := by
  simp [centroid_def, affineCombination_apply]
  -- 🎉 no goals
#align finset.centroid_singleton Finset.centroid_singleton

/-- The centroid of two points, expressed directly as adding a vector
to a point. -/
theorem centroid_pair [DecidableEq ι] [Invertible (2 : k)] (p : ι → P) (i₁ i₂ : ι) :
    ({i₁, i₂} : Finset ι).centroid k p = (2⁻¹ : k) • (p i₂ -ᵥ p i₁) +ᵥ p i₁ := by
  by_cases h : i₁ = i₂
  -- ⊢ centroid k {i₁, i₂} p = 2⁻¹ • (p i₂ -ᵥ p i₁) +ᵥ p i₁
  · simp [h]
    -- 🎉 no goals
  · have hc : (card ({i₁, i₂} : Finset ι) : k) ≠ 0 := by
      rw [card_insert_of_not_mem (not_mem_singleton.2 h), card_singleton]
      norm_num
      exact nonzero_of_invertible _
    rw [centroid_def,
      affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
        (sum_centroidWeights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)]
    simp [h, one_add_one_eq_two]
    -- 🎉 no goals
#align finset.centroid_pair Finset.centroid_pair

/-- The centroid of two points indexed by `Fin 2`, expressed directly
as adding a vector to the first point. -/
theorem centroid_pair_fin [Invertible (2 : k)] (p : Fin 2 → P) :
    univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 := by
  rw [univ_fin2]
  -- ⊢ centroid k {0, 1} p = 2⁻¹ • (p 1 -ᵥ p 0) +ᵥ p 0
  convert centroid_pair k p 0 1
  -- 🎉 no goals
#align finset.centroid_pair_fin Finset.centroid_pair_fin

/-- A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `Finset`. -/
theorem centroid_map (e : ι₂ ↪ ι) (p : ι → P) : (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) :=
  by simp [centroid_def, affineCombination_map, centroidWeights]
     -- 🎉 no goals
#align finset.centroid_map Finset.centroid_map

/-- `centroidWeights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `Fintype`, the sum may be over `univ`. -/
def centroidWeightsIndicator : ι → k :=
  Set.indicator (↑s) (s.centroidWeights k)
#align finset.centroid_weights_indicator Finset.centroidWeightsIndicator

/-- The definition of `centroidWeightsIndicator`. -/
theorem centroidWeightsIndicator_def :
    s.centroidWeightsIndicator k = Set.indicator (↑s) (s.centroidWeights k) :=
  rfl
#align finset.centroid_weights_indicator_def Finset.centroidWeightsIndicator_def

/-- The sum of the weights for the centroid indexed by a `Fintype`. -/
theorem sum_centroidWeightsIndicator [Fintype ι] :
    ∑ i, s.centroidWeightsIndicator k i = ∑ i in s, s.centroidWeights k i :=
  (Set.sum_indicator_subset _ (subset_univ _)).symm
#align finset.sum_centroid_weights_indicator Finset.sum_centroidWeightsIndicator

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is not
zero. -/
theorem sum_centroidWeightsIndicator_eq_one_of_card_ne_zero [CharZero k] [Fintype ι]
    (h : card s ≠ 0) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  -- ⊢ ∑ i in s, centroidWeights k s i = 1
  exact s.sum_centroidWeights_eq_one_of_card_ne_zero k h
  -- 🎉 no goals
#align finset.sum_centroid_weights_indicator_eq_one_of_card_ne_zero Finset.sum_centroidWeightsIndicator_eq_one_of_card_ne_zero

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the set is nonempty. -/
theorem sum_centroidWeightsIndicator_eq_one_of_nonempty [CharZero k] [Fintype ι] (h : s.Nonempty) :
    ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  -- ⊢ ∑ i in s, centroidWeights k s i = 1
  exact s.sum_centroidWeights_eq_one_of_nonempty k h
  -- 🎉 no goals
#align finset.sum_centroid_weights_indicator_eq_one_of_nonempty Finset.sum_centroidWeightsIndicator_eq_one_of_nonempty

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is `n + 1`. -/
theorem sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : ℕ}
    (h : card s = n + 1) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  -- ⊢ ∑ i in s, centroidWeights k s i = 1
  exact s.sum_centroidWeights_eq_one_of_card_eq_add_one k h
  -- 🎉 no goals
#align finset.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one Finset.sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one

/-- The centroid as an affine combination over a `Fintype`. -/
theorem centroid_eq_affineCombination_fintype [Fintype ι] (p : ι → P) :
    s.centroid k p = univ.affineCombination k p (s.centroidWeightsIndicator k) :=
  affineCombination_indicator_subset _ _ (subset_univ _)
#align finset.centroid_eq_affine_combination_fintype Finset.centroid_eq_affineCombination_fintype

/-- An indexed family of points that is injective on the given
`Finset` has the same centroid as the image of that `Finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
theorem centroid_eq_centroid_image_of_inj_on {p : ι → P}
    (hi : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), p i = p j → i = j) {ps : Set P} [Fintype ps]
    (hps : ps = p '' ↑s) : s.centroid k p = (univ : Finset ps).centroid k fun x => (x : P) := by
  let f : p '' ↑s → ι := fun x => x.property.choose
  -- ⊢ centroid k s p = centroid k univ fun x => ↑x
  have hf : ∀ x, f x ∈ s ∧ p (f x) = x := fun x => x.property.choose_spec
  -- ⊢ centroid k s p = centroid k univ fun x => ↑x
  let f' : ps → ι := fun x => f ⟨x, hps ▸ x.property⟩
  -- ⊢ centroid k s p = centroid k univ fun x => ↑x
  have hf' : ∀ x, f' x ∈ s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  -- ⊢ centroid k s p = centroid k univ fun x => ↑x
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff, ← (hf' x).2, ← (hf' y).2, h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  -- ⊢ centroid k s p = centroid k univ fun x => ↑x
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine' hi _ (hf' _).1 _ hx _
      rw [(hf' _).2]
  rw [← hu, centroid_map]
  -- ⊢ centroid k univ (p ∘ ↑f'e) = centroid k univ fun x => ↑x
  congr with x
  -- ⊢ (p ∘ ↑f'e) x = ↑x
  change p (f' x) = ↑x
  -- ⊢ p (f' x) = ↑x
  rw [(hf' x).2]
  -- 🎉 no goals
#align finset.centroid_eq_centroid_image_of_inj_on Finset.centroid_eq_centroid_image_of_inj_on

/-- Two indexed families of points that are injective on the given
`Finset`s and with the same points in the image of those `Finset`s
have the same centroid. -/
theorem centroid_eq_of_inj_on_of_image_eq {p : ι → P}
    (hi : ∀ (i) (_ : i ∈ s) (j) (_ : j ∈ s), p i = p j → i = j) {p₂ : ι₂ → P}
    (hi₂ : ∀ (i) (_ : i ∈ s₂) (j) (_ : j ∈ s₂), p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
    s.centroid k p = s₂.centroid k p₂ := by
  classical rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
      s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]
#align finset.centroid_eq_of_inj_on_of_image_eq Finset.centroid_eq_of_inj_on_of_image_eq

end Finset

section AffineSpace'

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- A `weightedVSub` with sum of weights 0 is in the `vectorSpan` of
an indexed family. -/
theorem weightedVSub_mem_vectorSpan {s : Finset ι} {w : ι → k} (h : ∑ i in s, w i = 0)
    (p : ι → P) : s.weightedVSub p w ∈ vectorSpan k (Set.range p) := by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_total,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p h (p i0),
        Finset.weightedVSubOfPoint_apply]
      let w' := Set.indicator (↑s) w
      have hwx : ∀ i, w' i ≠ 0 → i ∈ s := fun i => Set.mem_of_indicator_ne_zero
      use Finsupp.onFinset s w' hwx, Set.subset_univ _
      rw [Finsupp.total_apply, Finsupp.onFinset_sum hwx]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [Set.indicator_apply, if_pos hi]
      · exact fun _ => zero_smul k _
#align weighted_vsub_mem_vector_span weightedVSub_mem_vectorSpan

/-- An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the underlying ring is
nontrivial. -/
theorem affineCombination_mem_affineSpan [Nontrivial k] {s : Finset ι} {w : ι → k}
    (h : ∑ i in s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  classical
    have hnz : ∑ i in s, w i ≠ 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    cases' hn with i1 hi1
    let w1 : ι → k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i in s, w1 i = 1 := by
      simp only [Pi.const_zero, Finset.sum_update_of_mem hi1, Pi.zero_apply,
          Finset.sum_const_zero, add_zero]
    have hw1s : s.affineCombination k p w1 = p i1 :=
      s.affineCombination_of_eq_one_of_eq_zero w1 p hi1 (Function.update_same _ _ _) fun _ _ hne =>
        Function.update_noteq hne _ _
    have hv : s.affineCombination k p w -ᵥ p i1 ∈ (affineSpan k (Set.range p)).direction := by
      rw [direction_affineSpan, ← hw1s, Finset.affineCombination_vsub]
      apply weightedVSub_mem_vectorSpan
      -- Porting note: Rest was `simp [Pi.sub_apply, h, hw1]`,
      -- but `Pi.sub_apply` transforms the goal into nonsense
      change (Finset.sum s fun i => w i - w1 i) = 0
      simp only [Finset.sum_sub_distrib, h, hw1, sub_self]
    rw [← vsub_vadd (s.affineCombination k p w) (p i1)]
    exact AffineSubspace.vadd_mem_of_mem_direction hv (mem_affineSpan k (Set.mem_range_self _))
#align affine_combination_mem_affine_span affineCombination_mem_affineSpan

variable (k)

/-- A vector is in the `vectorSpan` of an indexed family if and only
if it is a `weightedVSub` with sum of weights 0. -/
theorem mem_vectorSpan_iff_eq_weightedVSub {v : V} {p : ι → P} :
    v ∈ vectorSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k) (_ : ∑ i in s, w i = 0), v = s.weightedVSub p w := by
  classical
    constructor
    · rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
      swap
      · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
          Finsupp.mem_span_image_iff_total]
        rintro ⟨l, _, hv⟩
        use insert i0 l.support
        set w :=
          (l : ι → k) - Function.update (Function.const ι 0 : ι → k) i0 (∑ i in l.support, l i) with
          hwdef
        use w
        have hw : ∑ i in insert i0 l.support, w i = 0 := by
          rw [hwdef]
          simp_rw [Pi.sub_apply, Finset.sum_sub_distrib,
            Finset.sum_update_of_mem (Finset.mem_insert_self _ _),
            Finset.sum_insert_of_eq_zero_if_not_mem Finsupp.not_mem_support_iff.1]
          simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_insert, true_or, not_true,
            Function.const_apply, Finset.sum_const_zero, add_zero, sub_self]
        use hw
        have hz : w i0 • (p i0 -ᵥ p i0 : V) = 0 := (vsub_self (p i0)).symm ▸ smul_zero _
        change (fun i => w i • (p i -ᵥ p i0 : V)) i0 = 0 at hz
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w p hw (p i0),
          Finset.weightedVSubOfPoint_apply, ← hv, Finsupp.total_apply,
          @Finset.sum_insert_zero _ _ l.support i0 _ _ _ hz]
        change (∑ i in l.support, l i • _) = _
        congr with i
        by_cases h : i = i0
        · simp [h]
        · simp [hwdef, h]
      · rw [Set.range_eq_empty, vectorSpan_empty, Submodule.mem_bot]
        rintro rfl
        use ∅
        simp
    · rintro ⟨s, w, hw, rfl⟩
      exact weightedVSub_mem_vectorSpan hw p
#align mem_vector_span_iff_eq_weighted_vsub mem_vectorSpan_iff_eq_weightedVSub

variable {k}

/-- A point in the `affineSpan` of an indexed family is an
`affineCombination` with sum of weights 1. See also
`eq_affineCombination_of_mem_affineSpan_of_fintype`. -/
theorem eq_affineCombination_of_mem_affineSpan {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ (s : Finset ι) (w : ι → k) (_ : ∑ i in s, w i = 1), p1 = s.affineCombination k p w := by
  classical
    have hn : (affineSpan k (Set.range p) : Set P).Nonempty := ⟨p1, h⟩
    rw [affineSpan_nonempty, Set.range_nonempty_iff_nonempty] at hn
    cases' hn with i0
    have h0 : p i0 ∈ affineSpan k (Set.range p) := mem_affineSpan k (Set.mem_range_self i0)
    have hd : p1 -ᵥ p i0 ∈ (affineSpan k (Set.range p)).direction :=
      AffineSubspace.vsub_mem_direction h h0
    rw [direction_affineSpan, mem_vectorSpan_iff_eq_weightedVSub] at hd
    rcases hd with ⟨s, w, h, hs⟩
    let s' := insert i0 s
    let w' := Set.indicator (↑s) w
    have h' : ∑ i in s', w' i = 0 := by
      rw [← h, Set.sum_indicator_subset _ (Finset.subset_insert i0 s)]
    have hs' : s'.weightedVSub p w' = p1 -ᵥ p i0 := by
      rw [hs]
      exact (Finset.weightedVSub_indicator_subset _ _ (Finset.subset_insert i0 s)).symm
    let w0 : ι → k := Function.update (Function.const ι 0) i0 1
    have hw0 : ∑ i in s', w0 i = 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_insert_self _ _)]
      simp only [Finset.mem_insert, true_or, not_true, Function.const_apply, Finset.sum_const_zero,
        add_zero]
    have hw0s : s'.affineCombination k p w0 = p i0 :=
      s'.affineCombination_of_eq_one_of_eq_zero w0 p (Finset.mem_insert_self _ _)
        (Function.update_same _ _ _) fun _ _ hne => Function.update_noteq hne _ _
    use s', w0 + w'
    constructor
    · rw [add_comm, ← Finset.weightedVSub_vadd_affineCombination, hw0s, hs', vsub_vadd]
    · -- Porting note: proof was `simp [Pi.add_apply, Finset.sum_add_distrib, hw0, h']`
      change (Finset.sum s' fun i => w0 i + w' i) = 1
      simp only [Finset.sum_add_distrib, hw0, h', add_zero]
#align eq_affine_combination_of_mem_affine_span eq_affineCombination_of_mem_affineSpan

theorem eq_affineCombination_of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ (w : ι → k) (_ : ∑ i, w i = 1), p1 = Finset.univ.affineCombination k p w := by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine'
      ⟨(s : Set ι).indicator w, _, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]
#align eq_affine_combination_of_mem_affine_span_of_fintype eq_affineCombination_of_mem_affineSpan_of_fintype

variable (k V)

/-- A point is in the `affineSpan` of an indexed family if and only
if it is an `affineCombination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
theorem mem_affineSpan_iff_eq_affineCombination [Nontrivial k] {p1 : P} {p : ι → P} :
    p1 ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k) (_ : ∑ i in s, w i = 1), p1 = s.affineCombination k p w := by
  constructor
  -- ⊢ p1 ∈ affineSpan k (Set.range p) → ∃ s w x, p1 = ↑(Finset.affineCombination k …
  · exact eq_affineCombination_of_mem_affineSpan
    -- 🎉 no goals
  · rintro ⟨s, w, hw, rfl⟩
    -- ⊢ ↑(Finset.affineCombination k s p) w ∈ affineSpan k (Set.range p)
    exact affineCombination_mem_affineSpan hw p
    -- 🎉 no goals
#align mem_affine_span_iff_eq_affine_combination mem_affineSpan_iff_eq_affineCombination

/-- Given a family of points together with a chosen base point in that family, membership of the
affine span of this family corresponds to an identity in terms of `weightedVSubOfPoint`, with
weights that are not required to sum to 1. -/
theorem mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd [Nontrivial k] (p : ι → P) (j : ι) (q : P) :
    q ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), q = s.weightedVSubOfPoint p (p j) w +ᵥ p j := by
  constructor
  -- ⊢ q ∈ affineSpan k (Set.range p) → ∃ s w, q = ↑(Finset.weightedVSubOfPoint s p …
  · intro hq
    -- ⊢ ∃ s w, q = ↑(Finset.weightedVSubOfPoint s p (p j)) w +ᵥ p j
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hq
    -- ⊢ ∃ s_1 w_1, ↑(Finset.affineCombination k s p) w = ↑(Finset.weightedVSubOfPoin …
    exact ⟨s, w, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw (p j)⟩
    -- 🎉 no goals
  · rintro ⟨s, w, rfl⟩
    -- ⊢ ↑(Finset.weightedVSubOfPoint s p (p j)) w +ᵥ p j ∈ affineSpan k (Set.range p)
    classical
      let w' : ι → k := Function.update w j (1 - (s \ {j}).sum w)
      have h₁ : (insert j s).sum w' = 1 := by
        by_cases hj : j ∈ s
        · simp [Finset.sum_update_of_mem hj, Finset.insert_eq_of_mem hj]
        · simp [Finset.sum_insert hj, Finset.sum_update_of_not_mem hj, hj]
      have hww : ∀ i, i ≠ j → w i = w' i := by
        intro i hij
        simp [hij]
      rw [s.weightedVSubOfPoint_eq_of_weights_eq p j w w' hww, ←
        s.weightedVSubOfPoint_insert w' p j, ←
        (insert j s).affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w' p h₁ (p j)]
      exact affineCombination_mem_affineSpan h₁ p
#align mem_affine_span_iff_eq_weighted_vsub_of_point_vadd mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd

variable {k V}

/-- Given a set of points, together with a chosen base point in this set, if we affinely transport
all other members of the set along the line joining them to this base point, the affine span is
unchanged. -/
theorem affineSpan_eq_affineSpan_lineMap_units [Nontrivial k] {s : Set P} {p : P} (hp : p ∈ s)
    (w : s → Units k) :
    affineSpan k (Set.range fun q : s => AffineMap.lineMap p ↑q (w q : k)) = affineSpan k s := by
  have : s = Set.range ((↑) : s → P) := by simp
  -- ⊢ affineSpan k (Set.range fun q => ↑(AffineMap.lineMap p ↑q) ↑(w q)) = affineS …
  conv_rhs =>
    rw [this]

  apply le_antisymm
    <;> intro q hq
    <;> erw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun x => μ x * ↑(w x)⁻¹]
    <;> simp [smul_smul]
        -- 🎉 no goals
        -- 🎉 no goals
#align affine_span_eq_affine_span_line_map_units affineSpan_eq_affineSpan_lineMap_units

end AffineSpace'

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AffineSpace V P] {ι : Type*}

open Set Finset

/-- The centroid lies in the affine span if the number of points,
converted to `k`, is not zero. -/
theorem centroid_mem_affineSpan_of_cast_card_ne_zero {s : Finset ι} (p : ι → P)
    (h : (card s : k) ≠ 0) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h) p
#align centroid_mem_affine_span_of_cast_card_ne_zero centroid_mem_affineSpan_of_cast_card_ne_zero

variable (k)

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero. -/
theorem centroid_mem_affineSpan_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι → P)
    (h : card s ≠ 0) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p
#align centroid_mem_affine_span_of_card_ne_zero centroid_mem_affineSpan_of_card_ne_zero

/-- In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty. -/
theorem centroid_mem_affineSpan_of_nonempty [CharZero k] {s : Finset ι} (p : ι → P)
    (h : s.Nonempty) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_nonempty k h) p
#align centroid_mem_affine_span_of_nonempty centroid_mem_affineSpan_of_nonempty

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`. -/
theorem centroid_mem_affineSpan_of_card_eq_add_one [CharZero k] {s : Finset ι} (p : ι → P) {n : ℕ}
    (h : card s = n + 1) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_eq_add_one k h) p
#align centroid_mem_affine_span_of_card_eq_add_one centroid_mem_affineSpan_of_card_eq_add_one

end DivisionRing

namespace AffineMap

variable {k : Type*} {V : Type*} (P : Type*) [CommRing k] [AddCommGroup V] [Module k V]

variable [AffineSpace V P] {ι : Type*} (s : Finset ι)

-- TODO: define `affineMap.proj`, `affineMap.fst`, `affineMap.snd`
/-- A weighted sum, as an affine map on the points involved. -/
def weightedVSubOfPoint (w : ι → k) : (ι → P) × P →ᵃ[k] V where
  toFun p := s.weightedVSubOfPoint p.fst p.snd w
  linear := ∑ i in s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _)
  map_vadd' := by
    rintro ⟨p, b⟩ ⟨v, b'⟩
    -- ⊢ (fun p => ↑(Finset.weightedVSubOfPoint s p.fst p.snd) w) ((v, b') +ᵥ (p, b)) …
    -- Porting note: needed to give `Prod.mk_vadd_mk` a hint
    simp [LinearMap.sum_apply, Finset.weightedVSubOfPoint, vsub_vadd_eq_vsub_sub,
     vadd_vsub_assoc,
     add_sub, ← sub_add_eq_add_sub, smul_add, Finset.sum_add_distrib, Prod.mk_vadd_mk v]
#align affine_map.weighted_vsub_of_point AffineMap.weightedVSubOfPoint

end AffineMap

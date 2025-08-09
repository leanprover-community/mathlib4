/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Algebra.Module.BigOperators
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.FinCases

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

open Affine

namespace Finset

theorem univ_fin2 : (univ : Finset (Fin 2)) = {0, 1} := by
  ext x
  fin_cases x <;> simp

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
  ∑ i ∈ s, (LinearMap.proj i : (ι → k) →ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]
theorem weightedVSubOfPoint_apply (w : ι → k) (p : ι → P) (b : P) :
    s.weightedVSubOfPoint p b w = ∑ i ∈ s, w i • (p i -ᵥ b) := by
  simp [weightedVSubOfPoint, LinearMap.sum_apply]

/-- The value of `weightedVSubOfPoint`, where the given points are equal. -/
@[simp (high)]
theorem weightedVSubOfPoint_apply_const (w : ι → k) (p : P) (b : P) :
    s.weightedVSubOfPoint (fun _ => p) b w = (∑ i ∈ s, w i) • (p -ᵥ b) := by
  rw [weightedVSubOfPoint_apply, sum_smul]

lemma weightedVSubOfPoint_vadd (s : Finset ι) (w : ι → k) (p : ι → P) (b : P) (v : V) :
    s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b) w := by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]

lemma weightedVSubOfPoint_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    (s : Finset ι) (w : ι → k) (p : ι → V) (b : V) (a : G) :
    s.weightedVSubOfPoint (a • p) b w = a • s.weightedVSubOfPoint p (a⁻¹ • b) w := by
  simp [smul_sum, smul_sub, smul_comm a (w _)]

/-- `weightedVSubOfPoint` gives equal results for two families of weights and two families of
points that are equal on `s`. -/
theorem weightedVSubOfPoint_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) (b : P) :
    s.weightedVSubOfPoint p₁ b w₁ = s.weightedVSubOfPoint p₂ b w₂ := by
  simp_rw [weightedVSubOfPoint_apply]
  refine sum_congr rfl fun i hi => ?_
  rw [hw i hi, hp i hi]

/-- Given a family of points, if we use a member of the family as a base point, the
`weightedVSubOfPoint` does not depend on the value of the weights at this point. -/
theorem weightedVSubOfPoint_eq_of_weights_eq (p : ι → P) (j : ι) (w₁ w₂ : ι → k)
    (hw : ∀ i, i ≠ j → w₁ i = w₂ i) :
    s.weightedVSubOfPoint p (p j) w₁ = s.weightedVSubOfPoint p (p j) w₂ := by
  simp only [Finset.weightedVSubOfPoint_apply]
  congr
  ext i
  rcases eq_or_ne i j with h | h
  · simp [h]
  · simp [hw i h]

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
theorem weightedVSubOfPoint_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i ∈ s, w i = 0)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w = s.weightedVSubOfPoint p b₂ w := by
  apply eq_of_sub_eq_zero
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← sum_sub_distrib]
  conv_lhs =>
    congr
    · skip
    · ext
      rw [← smul_sub, vsub_sub_vsub_cancel_left]
  rw [← sum_smul, h, zero_smul]

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
theorem weightedVSubOfPoint_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i ∈ s, w i = 1)
    (b₁ b₂ : P) : s.weightedVSubOfPoint p b₁ w +ᵥ b₁ = s.weightedVSubOfPoint p b₂ w +ᵥ b₂ := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← @vsub_eq_zero_iff_eq V,
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

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp (high)]
theorem weightedVSubOfPoint_erase [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (s.erase i).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  apply sum_erase
  rw [vsub_self, smul_zero]

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp (high)]
theorem weightedVSubOfPoint_insert [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
    (insert i s).weightedVSubOfPoint p (p i) w = s.weightedVSubOfPoint p (p i) w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  apply sum_insert_zero
  rw [vsub_self, smul_zero]

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weightedVSubOfPoint_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint p b (Set.indicator (↑s₁) w) := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply]
  exact Eq.symm <|
    sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

/-- A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`Finset`. -/
theorem weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
    (s₂.map e).weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint (p ∘ e) b (w ∘ e) := by
  simp_rw [weightedVSubOfPoint_apply]
  exact Finset.sum_map _ _ _

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two
`weightedVSubOfPoint` expressions. -/
theorem sum_smul_vsub_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ p₂ : ι → P) (b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.weightedVSubOfPoint p₁ b w - s.weightedVSubOfPoint p₂ b w := by
  simp_rw [weightedVSubOfPoint_apply, ← sum_sub_distrib, ← smul_sub, vsub_sub_vsub_cancel_right]

/-- A weighted sum of pairwise subtractions, where the point on the right is constant,
expressed as a subtraction involving a `weightedVSubOfPoint` expression. -/
theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ : ι → P) (p₂ b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ i ∈ s, w i) • (p₂ -ᵥ b) := by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const]

/-- A weighted sum of pairwise subtractions, where the point on the left is constant,
expressed as a subtraction involving a `weightedVSubOfPoint` expression. -/
theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι → k) (p₂ : ι → P) (p₁ b : P) :
    (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = (∑ i ∈ s, w i) • (p₁ -ᵥ b) - s.weightedVSubOfPoint p₂ b w := by
  rw [sum_smul_vsub_eq_weightedVSubOfPoint_sub, weightedVSubOfPoint_apply_const]

/-- A weighted sum may be split into such sums over two subsets. -/
theorem weightedVSubOfPoint_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w + s₂.weightedVSubOfPoint p b w =
      s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, sum_sdiff h]

/-- A weighted sum may be split into a subtraction of such sums over two subsets. -/
theorem weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w - s₂.weightedVSubOfPoint p b (-w) =
      s.weightedVSubOfPoint p b w := by
  rw [map_neg, sub_neg_eq_add, s.weightedVSubOfPoint_sdiff h]

/-- A weighted sum over `s.subtype pred` equals one over `{x ∈ s | pred x}`. -/
theorem weightedVSubOfPoint_subtype_eq_filter (w : ι → k) (p : ι → P) (b : P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSubOfPoint (fun i => p i) b fun i => w i) =
      {x ∈ s | pred x}.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, ← sum_subtype_eq_sum_filter]

/-- A weighted sum over `{x ∈ s | pred x}` equals one over `s` if all the weights at indices in `s`
not satisfying `pred` are zero. -/
theorem weightedVSubOfPoint_filter_of_ne (w : ι → k) (p : ι → P) (b : P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.weightedVSubOfPoint p b w = s.weightedVSubOfPoint p b w := by
  rw [weightedVSubOfPoint_apply, weightedVSubOfPoint_apply, sum_filter_of_ne]
  intro i hi hne
  refine h i hi ?_
  intro hw
  simp [hw] at hne

/-- A constant multiplier of the weights in `weightedVSubOfPoint` may be moved outside the
sum. -/
theorem weightedVSubOfPoint_const_smul (w : ι → k) (p : ι → P) (b : P) (c : k) :
    s.weightedVSubOfPoint p b (c • w) = c • s.weightedVSubOfPoint p b w := by
  simp_rw [weightedVSubOfPoint_apply, smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weightedVSub (p : ι → P) : (ι → k) →ₗ[k] V :=
  s.weightedVSubOfPoint p (Classical.choice S.nonempty)

/-- Applying `weightedVSub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weightedVSub` would involve selecting a preferred base point with
`weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` and then
using `weightedVSubOfPoint_apply`. -/
theorem weightedVSub_apply (w : ι → k) (p : ι → P) :
    s.weightedVSub p w = ∑ i ∈ s, w i • (p i -ᵥ Classical.choice S.nonempty) := by
  simp [weightedVSub]

/-- `weightedVSub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w :=
  s.weightedVSubOfPoint_eq_of_sum_eq_zero w p h _ _

/-- The value of `weightedVSub`, where the given points are equal and the sum of the weights
is 0. -/
@[simp]
theorem weightedVSub_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 0) :
    s.weightedVSub (fun _ => p) w = 0 := by
  rw [weightedVSub, weightedVSubOfPoint_apply_const, h, zero_smul]

/-- The `weightedVSub` for an empty set is 0. -/
@[simp]
theorem weightedVSub_empty (w : ι → k) (p : ι → P) : (∅ : Finset ι).weightedVSub p w = (0 : V) := by
  simp [weightedVSub_apply]

lemma weightedVSub_vadd {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → P) (v : V) :
    s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w := by
  rw [weightedVSub, weightedVSubOfPoint_vadd,
    weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

lemma weightedVSub_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → V) (a : G) :
    s.weightedVSub (a • p) w = a • s.weightedVSub p w := by
  rw [weightedVSub, weightedVSubOfPoint_smul,
    weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

/-- `weightedVSub` gives equal results for two families of weights and two families of points
that are equal on `s`. -/
theorem weightedVSub_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.weightedVSub p₁ w₁ = s.weightedVSub p₂ w₂ :=
  s.weightedVSubOfPoint_congr hw hp _

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weightedVSub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
    s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (↑s₁) w) :=
  weightedVSubOfPoint_indicator_subset _ _ _ h

/-- A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `Finset`. -/
theorem weightedVSub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e) :=
  s₂.weightedVSubOfPoint_map _ _ _ _

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two `weightedVSub`
expressions. -/
theorem sum_smul_vsub_eq_weightedVSub_sub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w :=
  s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

/-- A weighted sum of pairwise subtractions, where the point on the right is constant and the
sum of the weights is 0. -/
theorem sum_smul_vsub_const_eq_weightedVSub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSub p₁ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub, s.weightedVSub_apply_const _ _ h, sub_zero]

/-- A weighted sum of pairwise subtractions, where the point on the left is constant and the
sum of the weights is 0. -/
theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  rw [sum_smul_vsub_eq_weightedVSub_sub, s.weightedVSub_apply_const _ _ h, zero_sub]

/-- A weighted sum may be split into such sums over two subsets. -/
theorem weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k) (p : ι → P) :
    (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff h _ _ _

/-- A weighted sum may be split into a subtraction of such sums over two subsets. -/
theorem weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) = s.weightedVSub p w :=
  s.weightedVSubOfPoint_sdiff_sub h _ _ _

/-- A weighted sum over `s.subtype pred` equals one over `{x ∈ s | pred x}`. -/
theorem weightedVSub_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSub (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.weightedVSub p w :=
  s.weightedVSubOfPoint_subtype_eq_filter _ _ _ _

/-- A weighted sum over `{x ∈ s | pred x}` equals one over `s` if all the weights at indices in `s`
not satisfying `pred` are zero. -/
theorem weightedVSub_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop} [DecidablePred pred]
    (h : ∀ i ∈ s, w i ≠ 0 → pred i) : {x ∈ s | pred x}.weightedVSub p w = s.weightedVSub p w :=
  s.weightedVSubOfPoint_filter_of_ne _ _ _ h

/-- A constant multiplier of the weights in `weightedVSub_of` may be moved outside the sum. -/
theorem weightedVSub_const_smul (w : ι → k) (p : ι → P) (c : k) :
    s.weightedVSub p (c • w) = c • s.weightedVSub p w :=
  s.weightedVSubOfPoint_const_smul _ _ _ _

instance : AffineSpace (ι → k) (ι → k) := Pi.instAddTorsor

variable (k)

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it. -/
def affineCombination (p : ι → P) : (ι → k) →ᵃ[k] P where
  toFun w := s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty
  linear := s.weightedVSub p
  map_vadd' w₁ w₂ := by simp_rw [vadd_vadd, weightedVSub, vadd_eq_add, LinearMap.map_add]

/-- The linear map corresponding to `affineCombination` is
`weightedVSub`. -/
@[simp]
theorem affineCombination_linear (p : ι → P) :
    (s.affineCombination k p).linear = s.weightedVSub p :=
  rfl

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
      s.weightedVSubOfPoint p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty :=
  rfl

/-- The value of `affineCombination`, where the given points are equal. -/
@[simp]
theorem affineCombination_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 1) :
    s.affineCombination k (fun _ => p) w = p := by
  rw [affineCombination_apply, s.weightedVSubOfPoint_apply_const, h, one_smul, vsub_vadd]

/-- `affineCombination` gives equal results for two families of weights and two families of
points that are equal on `s`. -/
theorem affineCombination_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.affineCombination k p₁ w₁ = s.affineCombination k p₂ w₂ := by
  simp_rw [affineCombination_apply, s.weightedVSubOfPoint_congr hw hp]

/-- `affineCombination` gives the sum with any base point, when the
sum of the weights is 1. -/
theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 1) (b : P) :
    s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b :=
  s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w p h _ _

/-- Adding a `weightedVSub` to an `affineCombination`. -/
theorem weightedVSub_vadd_affineCombination (w₁ w₂ : ι → k) (p : ι → P) :
    s.weightedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂) := by
  rw [← vadd_eq_add, AffineMap.map_vadd, affineCombination_linear]

/-- Subtracting two `affineCombination`s. -/
theorem affineCombination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
    s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weightedVSub p (w₁ - w₂) := by
  rw [← AffineMap.linearMap_vsub, affineCombination_linear, vsub_eq_sub]

theorem attach_affineCombination_of_injective [DecidableEq P] (s : Finset P) (w : P → k) (f : s → P)
    (hf : Function.Injective f) :
    s.attach.affineCombination k f (w ∘ f) = (image f univ).affineCombination k id w := by
  simp only [affineCombination, weightedVSubOfPoint_apply, id, vadd_right_cancel_iff,
    Function.comp_apply, AffineMap.coe_mk]
  let g₁ : s → V := fun i => w (f i) • (f i -ᵥ Classical.choice S.nonempty)
  let g₂ : P → V := fun i => w i • (i -ᵥ Classical.choice S.nonempty)
  change univ.sum g₁ = (image f univ).sum g₂
  have hgf : g₁ = g₂ ∘ f := by
    ext
    simp [g₁, g₂]
  rw [hgf, sum_image]
  · simp only [g₂,Function.comp_apply]
  · exact fun _ _ _ _ hxy => hf hxy

theorem attach_affineCombination_coe (s : Finset P) (w : P → k) :
    s.attach.affineCombination k ((↑) : s → P) (w ∘ (↑)) = s.affineCombination k id w := by
  classical rw [attach_affineCombination_of_injective s w ((↑) : s → P) Subtype.coe_injective,
      univ_eq_attach, attach_image_val]

/-- Viewing a module as an affine space modelled on itself, a `weightedVSub` is just a linear
combination. -/
@[simp]
theorem weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι → k} {p : ι → V}
    (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i ∈ s, w i • p i := by
  simp [s.weightedVSub_apply, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]

/-- Viewing a module as an affine space modelled on itself, affine combinations are just linear
combinations. -/
@[simp]
theorem affineCombination_eq_linear_combination (s : Finset ι) (p : ι → V) (w : ι → k)
    (hw : ∑ i ∈ s, w i = 1) : s.affineCombination k p w = ∑ i ∈ s, w i • p i := by
  simp [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw 0]

/-- An `affineCombination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
-- Cannot be @[simp] because `i` can not be inferred by `simp`.
theorem affineCombination_of_eq_one_of_eq_zero (w : ι → k) (p : ι → P) {i : ι} (his : i ∈ s)
    (hwi : w i = 1) (hw0 : ∀ i2 ∈ s, i2 ≠ i → w i2 = 0) : s.affineCombination k p w = p i := by
  have h1 : ∑ i ∈ s, w i = 1 := hwi ▸ sum_eq_single i hw0 fun h => False.elim (h his)
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h1 (p i),
    weightedVSubOfPoint_apply]
  convert zero_vadd V (p i)
  refine sum_eq_zero ?_
  intro i2 hi2
  by_cases h : i2 = i
  · simp [h]
  · simp [hw0 i2 hi2 h]

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem affineCombination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.affineCombination k p w = s₂.affineCombination k p (Set.indicator (↑s₁) w) := by
  rw [affineCombination_apply, affineCombination_apply,
    weightedVSubOfPoint_indicator_subset _ _ _ h]

/-- An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`Finset`. -/
theorem affineCombination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).affineCombination k p w = s₂.affineCombination k (p ∘ e) (w ∘ e) := by
  simp_rw [affineCombination_apply, weightedVSubOfPoint_map]

/-- A weighted sum of pairwise subtractions, expressed as a subtraction of two `affineCombination`
expressions. -/
theorem sum_smul_vsub_eq_affineCombination_vsub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.affineCombination k p₁ w -ᵥ s.affineCombination k p₂ w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.sum_smul_vsub_eq_weightedVSubOfPoint_sub _ _ _ _

/-- A weighted sum of pairwise subtractions, where the point on the right is constant and the
sum of the weights is 1. -/
theorem sum_smul_vsub_const_eq_affineCombination_vsub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.affineCombination k p₁ w -ᵥ p₂ := by
  rw [sum_smul_vsub_eq_affineCombination_vsub, affineCombination_apply_const _ _ _ h]

/-- A weighted sum of pairwise subtractions, where the point on the left is constant and the
sum of the weights is 1. -/
theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w := by
  rw [sum_smul_vsub_eq_affineCombination_vsub, affineCombination_apply_const _ _ _ h]

/-- A weighted sum may be split into a subtraction of affine combinations over two subsets. -/
theorem affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) :
    (s \ s₂).affineCombination k p w -ᵥ s₂.affineCombination k p (-w) = s.weightedVSub p w := by
  simp_rw [affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact s.weightedVSub_sdiff_sub h _ _

/-- If a weighted sum is zero and one of the weights is `-1`, the corresponding point is
the affine combination of the other points with the given weights. -/
theorem affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι → k} {p : ι → P}
    (hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidablePred (· ≠ i)] (his : i ∈ s)
    (hwi : w i = -1) : {x ∈ s | x ≠ i}.affineCombination k p w = p i := by
  classical
    rw [← @vsub_eq_zero_iff_eq V, ← hw,
      ← s.affineCombination_sdiff_sub (singleton_subset_iff.2 his), sdiff_singleton_eq_erase,
      ← filter_ne']
    congr
    refine (affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) ?_ ?_).symm
    · simp [hwi]
    · simp

/-- An affine combination over `s.subtype pred` equals one over `{x ∈ s | pred x}`. -/
theorem affineCombination_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).affineCombination k (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.affineCombination k p w := by
  rw [affineCombination_apply, affineCombination_apply, weightedVSubOfPoint_subtype_eq_filter]

/-- An affine combination over `{x ∈ s | pred x}` equals one over `s` if all the weights at indices
in `s` not satisfying `pred` are zero. -/
theorem affineCombination_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.affineCombination k p w = s.affineCombination k p w := by
  rw [affineCombination_apply, affineCombination_apply,
    s.weightedVSubOfPoint_filter_of_ne _ _ _ h]

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weightedVSubOfPoint` using a `Finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weightedVSubOfPoint` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k} {s : Set ι}
    {p : ι → P} {b : P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = x ∧
        v = fs.weightedVSubOfPoint p b w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = x ∧
        v = fs.weightedVSubOfPoint (fun i : s => p i) b w := by
  classical
    simp_rw [weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype s, fun i => w i, sum_subtype_of_mem _ hfs, (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine
          ⟨fs.map (Function.Embedding.subtype _), map_subtype_subset _, fun i =>
            if h : i ∈ s then w ⟨i, h⟩ else 0, ?_, ?_⟩ <;>
        simp

variable (k)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weightedVSub` using
a `Finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weightedVSub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weightedVSub_subset_iff_eq_weightedVSub_subtype {v : V} {s : Set ι} {p : ι → P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = 0 ∧
        v = fs.weightedVSub p w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = 0 ∧
        v = fs.weightedVSub (fun i : s => p i) w :=
  eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

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
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = 1 ∧
        p0 = fs.affineCombination k p w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = 1 ∧
        p0 = fs.affineCombination k (fun i : s => p i) w := by
  simp_rw [affineCombination_apply, eq_vadd_iff_vsub_eq]
  exact eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

variable {k V}

/-- Affine maps commute with affine combinations. -/
theorem map_affineCombination {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]
    (p : ι → P) (w : ι → k) (hw : s.sum w = 1) (f : P →ᵃ[k] P₂) :
    f (s.affineCombination k p w) = s.affineCombination k (f ∘ p) w := by
  have b := Classical.choice (inferInstance : AffineSpace V P).nonempty
  have b₂ := Classical.choice (inferInstance : AffineSpace V₂ P₂).nonempty
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw b,
    s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w (f ∘ p) hw b₂, ←
    s.weightedVSubOfPoint_vadd_eq_of_sum_eq_one w (f ∘ p) hw (f b) b₂]
  simp only [weightedVSubOfPoint_apply, RingHom.id_apply, AffineMap.map_vadd,
    LinearMap.map_smulₛₗ, AffineMap.linearMap_vsub, map_sum, Function.comp_apply]

/-- The value of `affineCombination`, where the given points take only two values. -/
lemma affineCombination_apply_eq_lineMap_sum [DecidableEq ι] (w : ι → k) (p : ι → P)
    (p₁ p₂ : P) (s' : Finset ι) (h : ∑ i ∈ s, w i = 1) (hp₂ : ∀ i ∈ s ∩ s', p i = p₂)
    (hp₁ : ∀ i ∈ s \ s', p i = p₁) :
    s.affineCombination k p w = AffineMap.lineMap p₁ p₂ (∑ i ∈ s ∩ s', w i) := by
  rw [s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p h p₁,
    weightedVSubOfPoint_apply, ← s.sum_inter_add_sum_diff s', AffineMap.lineMap_apply,
    vadd_right_cancel_iff, sum_smul]
  convert add_zero _ with i hi
  · convert Finset.sum_const_zero with i hi
    simp [hp₁ i hi]
  · exact (hp₂ i hi).symm

variable (k)

/-- Weights for expressing a single point as an affine combination. -/
def affineCombinationSingleWeights [DecidableEq ι] (i : ι) : ι → k :=
  Pi.single i 1

@[simp]
theorem affineCombinationSingleWeights_apply_self [DecidableEq ι] (i : ι) :
    affineCombinationSingleWeights k i i = 1 := Pi.single_eq_same _ _

@[simp]
theorem affineCombinationSingleWeights_apply_of_ne [DecidableEq ι] {i j : ι} (h : j ≠ i) :
    affineCombinationSingleWeights k i j = 0 := Pi.single_eq_of_ne h _

@[simp]
theorem sum_affineCombinationSingleWeights [DecidableEq ι] {i : ι} (h : i ∈ s) :
    ∑ j ∈ s, affineCombinationSingleWeights k i j = 1 := by
  rw [← affineCombinationSingleWeights_apply_self k i]
  exact sum_eq_single_of_mem i h fun j _ hj => affineCombinationSingleWeights_apply_of_ne k hj

/-- Weights for expressing the subtraction of two points as a `weightedVSub`. -/
def weightedVSubVSubWeights [DecidableEq ι] (i j : ι) : ι → k :=
  affineCombinationSingleWeights k i - affineCombinationSingleWeights k j

@[simp]
theorem weightedVSubVSubWeights_self [DecidableEq ι] (i : ι) :
    weightedVSubVSubWeights k i i = 0 := by simp [weightedVSubVSubWeights]

@[simp]
theorem weightedVSubVSubWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    weightedVSubVSubWeights k i j i = 1 := by simp [weightedVSubVSubWeights, h]

@[simp]
theorem weightedVSubVSubWeights_apply_right [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    weightedVSubVSubWeights k i j j = -1 := by simp [weightedVSubVSubWeights, h.symm]

@[simp]
theorem weightedVSubVSubWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i) (hj : t ≠ j) :
    weightedVSubVSubWeights k i j t = 0 := by simp [weightedVSubVSubWeights, hi, hj]

@[simp]
theorem sum_weightedVSubVSubWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    ∑ t ∈ s, weightedVSubVSubWeights k i j t = 0 := by
  simp_rw [weightedVSubVSubWeights, Pi.sub_apply, sum_sub_distrib]
  simp [hi, hj]

variable {k}

/-- Weights for expressing `lineMap` as an affine combination. -/
def affineCombinationLineMapWeights [DecidableEq ι] (i j : ι) (c : k) : ι → k :=
  c • weightedVSubVSubWeights k j i + affineCombinationSingleWeights k i

@[simp]
theorem affineCombinationLineMapWeights_self [DecidableEq ι] (i : ι) (c : k) :
    affineCombinationLineMapWeights i i c = affineCombinationSingleWeights k i := by
  simp [affineCombinationLineMapWeights]

@[simp]
theorem affineCombinationLineMapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    affineCombinationLineMapWeights i j c i = 1 - c := by
  simp [affineCombinationLineMapWeights, h.symm, sub_eq_neg_add]

@[simp]
theorem affineCombinationLineMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i ≠ j) (c : k) :
    affineCombinationLineMapWeights i j c j = c := by
  simp [affineCombinationLineMapWeights, h.symm]

@[simp]
theorem affineCombinationLineMapWeights_apply_of_ne [DecidableEq ι] {i j t : ι} (hi : t ≠ i)
    (hj : t ≠ j) (c : k) : affineCombinationLineMapWeights i j c t = 0 := by
  simp [affineCombinationLineMapWeights, hi, hj]

@[simp]
theorem sum_affineCombinationLineMapWeights [DecidableEq ι] {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (c : k) : ∑ t ∈ s, affineCombinationLineMapWeights i j c t = 1 := by
  simp_rw [affineCombinationLineMapWeights, Pi.add_apply, sum_add_distrib]
  simp [hi, hj, ← mul_sum]

variable (k)

/-- An affine combination with `affineCombinationSingleWeights` gives the specified point. -/
@[simp]
theorem affineCombination_affineCombinationSingleWeights [DecidableEq ι] (p : ι → P) {i : ι}
    (hi : i ∈ s) : s.affineCombination k p (affineCombinationSingleWeights k i) = p i := by
  refine s.affineCombination_of_eq_one_of_eq_zero _ _ hi (by simp) ?_
  rintro j - hj
  simp [hj]

/-- A weighted subtraction with `weightedVSubVSubWeights` gives the result of subtracting the
specified points. -/
@[simp]
theorem weightedVSub_weightedVSubVSubWeights [DecidableEq ι] (p : ι → P) {i j : ι} (hi : i ∈ s)
    (hj : j ∈ s) : s.weightedVSub p (weightedVSubVSubWeights k i j) = p i -ᵥ p j := by
  rw [weightedVSubVSubWeights, ← affineCombination_vsub,
    s.affineCombination_affineCombinationSingleWeights k p hi,
    s.affineCombination_affineCombinationSingleWeights k p hj]

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

end Finset

section AffineSpace'

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- A `weightedVSub` with sum of weights 0 is in the `vectorSpan` of
an indexed family. -/
theorem weightedVSub_mem_vectorSpan {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0)
    (p : ι → P) : s.weightedVSub p w ∈ vectorSpan k (Set.range p) := by
  classical
    rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
    · simp [Finset.eq_empty_of_isEmpty s]
    · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
        Finsupp.mem_span_image_iff_linearCombination,
        Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p h (p i0),
        Finset.weightedVSubOfPoint_apply]
      let w' := Set.indicator (↑s) w
      have hwx : ∀ i, w' i ≠ 0 → i ∈ s := fun i => Set.mem_of_indicator_ne_zero
      use Finsupp.onFinset s w' hwx, Set.subset_univ _
      rw [Finsupp.linearCombination_apply, Finsupp.onFinset_sum hwx]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [w', Set.indicator_apply, if_pos hi]
      · exact fun _ => zero_smul k _

/-- An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the underlying ring is
nontrivial. -/
theorem affineCombination_mem_affineSpan [Nontrivial k] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  classical
    have hnz : ∑ i ∈ s, w i ≠ 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    obtain ⟨i1, hi1⟩ := hn
    let w1 : ι → k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i ∈ s, w1 i = 1 := by
      simp only [w1, Function.const_zero, Finset.sum_update_of_mem hi1, Pi.zero_apply,
          Finset.sum_const_zero, add_zero]
    have hw1s : s.affineCombination k p w1 = p i1 :=
      s.affineCombination_of_eq_one_of_eq_zero w1 p hi1 (Function.update_self ..) fun _ _ hne =>
        Function.update_of_ne hne ..
    have hv : s.affineCombination k p w -ᵥ p i1 ∈ (affineSpan k (Set.range p)).direction := by
      rw [direction_affineSpan, ← hw1s, Finset.affineCombination_vsub]
      apply weightedVSub_mem_vectorSpan
      simp [Pi.sub_apply, h, hw1]
    rw [← vsub_vadd (s.affineCombination k p w) (p i1)]
    exact AffineSubspace.vadd_mem_of_mem_direction hv (mem_affineSpan k (Set.mem_range_self _))

/-- An `affineCombination` with sum of weights 1 is in the
`affineSpan` of an indexed family, if the family is nonempty. -/
theorem affineCombination_mem_affineSpan_of_nonempty [Nonempty ι] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  rcases subsingleton_or_nontrivial k with hs | hn
  · have hnv := Module.subsingleton k V
    rw [AddTorsor.subsingleton_iff V P] at hnv
    rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (Set.range_nonempty p)]
    simp
  · exact affineCombination_mem_affineSpan h p

variable (k) in
/-- A vector is in the `vectorSpan` of an indexed family if and only
if it is a `weightedVSub` with sum of weights 0. -/
theorem mem_vectorSpan_iff_eq_weightedVSub {v : V} {p : ι → P} :
    v ∈ vectorSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 0 ∧ v = s.weightedVSub p w := by
  classical
    constructor
    · rcases isEmpty_or_nonempty ι with (hι | ⟨⟨i0⟩⟩)
      swap
      · rw [vectorSpan_range_eq_span_range_vsub_right k p i0, ← Set.image_univ,
          Finsupp.mem_span_image_iff_linearCombination]
        rintro ⟨l, _, hv⟩
        use insert i0 l.support
        set w :=
          (l : ι → k) - Function.update (Function.const ι 0 : ι → k) i0 (∑ i ∈ l.support, l i) with
          hwdef
        use w
        have hw : ∑ i ∈ insert i0 l.support, w i = 0 := by
          rw [hwdef]
          simp_rw [Pi.sub_apply, Finset.sum_sub_distrib,
            Finset.sum_update_of_mem (Finset.mem_insert_self _ _),
            Finset.sum_insert_of_eq_zero_if_notMem Finsupp.notMem_support_iff.1]
          simp only [Function.const_apply, Finset.sum_const_zero, add_zero, sub_self]
        use hw
        have hz : w i0 • (p i0 -ᵥ p i0 : V) = 0 := (vsub_self (p i0)).symm ▸ smul_zero _
        change (fun i => w i • (p i -ᵥ p i0 : V)) i0 = 0 at hz
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w p hw (p i0),
          Finset.weightedVSubOfPoint_apply, ← hv, Finsupp.linearCombination_apply,
          @Finset.sum_insert_zero _ _ l.support i0 _ _ _ hz]
        change (∑ i ∈ l.support, l i • _) = _
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

/-- A point in the `affineSpan` of an indexed family is an
`affineCombination` with sum of weights 1. See also
`eq_affineCombination_of_mem_affineSpan_of_fintype`. -/
theorem eq_affineCombination_of_mem_affineSpan {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  classical
    have hn : (affineSpan k (Set.range p) : Set P).Nonempty := ⟨p1, h⟩
    rw [affineSpan_nonempty, Set.range_nonempty_iff_nonempty] at hn
    obtain ⟨i0⟩ := hn
    have h0 : p i0 ∈ affineSpan k (Set.range p) := mem_affineSpan k (Set.mem_range_self i0)
    have hd : p1 -ᵥ p i0 ∈ (affineSpan k (Set.range p)).direction :=
      AffineSubspace.vsub_mem_direction h h0
    rw [direction_affineSpan, mem_vectorSpan_iff_eq_weightedVSub] at hd
    rcases hd with ⟨s, w, h, hs⟩
    let s' := insert i0 s
    let w' := Set.indicator (↑s) w
    have h' : ∑ i ∈ s', w' i = 0 := by
      rw [← h, Finset.sum_indicator_subset _ (Finset.subset_insert i0 s)]
    have hs' : s'.weightedVSub p w' = p1 -ᵥ p i0 := by
      rw [hs]
      exact (Finset.weightedVSub_indicator_subset _ _ (Finset.subset_insert i0 s)).symm
    let w0 : ι → k := Function.update (Function.const ι 0) i0 1
    have hw0 : ∑ i ∈ s', w0 i = 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_insert_self _ _)]
      simp only [Function.const_apply, Finset.sum_const_zero,
        add_zero]
    have hw0s : s'.affineCombination k p w0 = p i0 :=
      s'.affineCombination_of_eq_one_of_eq_zero w0 p (Finset.mem_insert_self _ _)
        (Function.update_self ..) fun _ _ hne => Function.update_of_ne hne _ _
    refine ⟨s', w0 + w', ?_, ?_⟩
    · simp [Pi.add_apply, Finset.sum_add_distrib, hw0, h']
    · rw [add_comm, ← Finset.weightedVSub_vadd_affineCombination, hw0s, hs', vsub_vadd]

theorem eq_affineCombination_of_mem_affineSpan_of_fintype [Fintype ι] {p1 : P} {p : ι → P}
    (h : p1 ∈ affineSpan k (Set.range p)) :
    ∃ w : ι → k, ∑ i, w i = 1 ∧ p1 = Finset.univ.affineCombination k p w := by
  classical
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan h
    refine
      ⟨(s : Set ι).indicator w, ?_, Finset.affineCombination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ← hw]
    rw [Fintype.sum_extend_by_zero s w]

/-- A point in the `affineSpan` of a subset of an indexed family is an
`affineCombination` with sum of weights 1, using only points in the given subset. -/
lemma eq_affineCombination_of_mem_affineSpan_image {p₁ : P} {p : ι → P} {s : Set ι}
    (h : p₁ ∈ affineSpan k (p '' s)) :
    ∃ (fs : Finset ι) (w : ι → k), ↑fs ⊆ s ∧ ∑ i ∈ fs, w i = 1 ∧
      p₁ = fs.affineCombination k p w := by
  classical
  rw [Set.image_eq_range] at h
  obtain ⟨fs', w', hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan h
  refine ⟨fs'.map (Function.Embedding.subtype _), fun i ↦ if hi : i ∈ s then w' ⟨i, hi⟩ else 0,
    (by simp), (by simp [hw']), ?_⟩
  simp only [Finset.affineCombination_map, Function.Embedding.coe_subtype]
  exact fs'.affineCombination_congr (by simp) (by simp)

variable (k V)

/-- A point is in the `affineSpan` of an indexed family if and only
if it is an `affineCombination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
theorem mem_affineSpan_iff_eq_affineCombination [Nontrivial k] {p1 : P} {p : ι → P} :
    p1 ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  constructor
  · exact eq_affineCombination_of_mem_affineSpan
  · rintro ⟨s, w, hw, rfl⟩
    exact affineCombination_mem_affineSpan hw p

/-- Given a family of points together with a chosen base point in that family, membership of the
affine span of this family corresponds to an identity in terms of `weightedVSubOfPoint`, with
weights that are not required to sum to 1. -/
theorem mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd [Nontrivial k] (p : ι → P) (j : ι) (q : P) :
    q ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), q = s.weightedVSubOfPoint p (p j) w +ᵥ p j := by
  constructor
  · intro hq
    obtain ⟨s, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hq
    exact ⟨s, w, s.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w p hw (p j)⟩
  · rintro ⟨s, w, rfl⟩
    classical
      let w' : ι → k := Function.update w j (1 - (s \ {j}).sum w)
      have h₁ : (insert j s).sum w' = 1 := by
        by_cases hj : j ∈ s
        · simp [w', Finset.sum_update_of_mem hj, Finset.insert_eq_of_mem hj]
        · simp_rw [w', Finset.sum_insert hj, Finset.sum_update_of_notMem hj, Function.update_self,
            ← Finset.erase_eq, Finset.erase_eq_of_notMem hj, sub_add_cancel]
      have hww : ∀ i, i ≠ j → w i = w' i := by
        intro i hij
        simp [w', hij]
      rw [s.weightedVSubOfPoint_eq_of_weights_eq p j w w' hww, ←
        s.weightedVSubOfPoint_insert w' p j, ←
        (insert j s).affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one w' p h₁ (p j)]
      exact affineCombination_mem_affineSpan h₁ p

variable {k V}

/-- Given a set of points, together with a chosen base point in this set, if we affinely transport
all other members of the set along the line joining them to this base point, the affine span is
unchanged. -/
theorem affineSpan_eq_affineSpan_lineMap_units [Nontrivial k] {s : Set P} {p : P} (hp : p ∈ s)
    (w : s → Units k) :
    affineSpan k (Set.range fun q : s => AffineMap.lineMap p ↑q (w q : k)) = affineSpan k s := by
  have : s = Set.range ((↑) : s → P) := by simp
  conv_rhs =>
    rw [this]
  apply le_antisymm
    <;> intro q hq
    <;> erw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun x => μ x * ↑(w x)⁻¹]
    <;> simp [smul_smul]

end AffineSpace'

namespace AffineMap

variable {k : Type*} {V : Type*} (P : Type*) [CommRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*} (s : Finset ι)

-- TODO: define `affineMap.proj`, `affineMap.fst`, `affineMap.snd`
/-- A weighted sum, as an affine map on the points involved. -/
def weightedVSubOfPoint (w : ι → k) : (ι → P) × P →ᵃ[k] V where
  toFun p := s.weightedVSubOfPoint p.fst p.snd w
  linear := ∑ i ∈ s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _)
  map_vadd' := by
    rintro ⟨p, b⟩ ⟨v, b'⟩
    simp [LinearMap.sum_apply, Finset.weightedVSubOfPoint, vsub_vadd_eq_vsub_sub,
     vadd_vsub_assoc, ← sub_add_eq_add_sub, smul_add, Finset.sum_add_distrib]

end AffineMap

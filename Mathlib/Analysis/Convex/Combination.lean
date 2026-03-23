/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `Finset.centerMass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `Finset.centerMass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/

@[expose] public section

assert_not_exists Cardinal

open Set Function Pointwise

universe u u'

section
variable {R R' E F ι ι' α : Type*} [Field R] [Field R'] [AddCommGroup E] [AddCommGroup F]
  [AddCommGroup α] [LinearOrder α] [Module R E] [Module R F] [Module R α] {s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i ∈ t, w i)⁻¹ • ∑ i ∈ t, w i • z i

variable (i j : ι) (c : R) (t : Finset ι) (w : ι → R) (z : ι → E)

open Finset

theorem Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0 := by
  simp only [centerMass, sum_empty, smul_zero]

theorem Finset.centerMass_pair [DecidableEq ι] (hne : i ≠ j) :
    ({i, j} : Finset ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [centerMass, sum_pair hne]
  module

variable {w}

theorem Finset.centerMass_insert [DecidableEq ι] (ha : i ∉ t) (hw : ∑ j ∈ t, w j ≠ 0) :
    (insert i t).centerMass w z =
      (w i / (w i + ∑ j ∈ t, w j)) • z i +
        ((∑ j ∈ t, w j) / (w i + ∑ j ∈ t, w j)) • t.centerMass w z := by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hw, one_div]

theorem Finset.centerMass_singleton (hw : w i ≠ 0) : ({i} : Finset ι).centerMass w z = z i := by
  rw [centerMass, sum_singleton, sum_singleton]
  match_scalars
  field

@[simp] lemma Finset.centerMass_neg_left : t.centerMass (-w) z = t.centerMass w z := by
  simp [centerMass, inv_neg]

lemma Finset.centerMass_smul_left {c : R'} [Module R' R] [Module R' E] [SMulCommClass R' R R]
    [IsScalarTower R' R R] [SMulCommClass R R' E] [IsScalarTower R' R E] (hc : c ≠ 0) :
    t.centerMass (c • w) z = t.centerMass w z := by
  simp [centerMass, -smul_assoc, smul_assoc c, ← smul_sum, smul_inv₀, smul_smul_smul_comm, hc]

theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i ∈ t, w i = 1) :
    t.centerMass w z = ∑ i ∈ t, w i • z i := by
  simp only [Finset.centerMass, hw, inv_one, one_smul]

theorem Finset.centerMass_smul : (t.centerMass w fun i => c • z i) = c • t.centerMass w z := by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι → R) (zs : ι → E)
    (wt : ι' → R) (zt : ι' → E) (hws : ∑ i ∈ s, ws i = 1) (hwt : ∑ i ∈ t, wt i = 1) (a b : R)
    (hab : a + b = 1) : a • s.centerMass ws zs + b • t.centerMass wt zt = (s.disjSum t).centerMass
    (Sum.elim (fun i => a * ws i) fun j => b * wt j) (Sum.elim zs zt) := by
  rw [s.centerMass_eq_of_sum_1 _ hws, t.centerMass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ←
    Finset.sum_sumElim, Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sumElim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι → R) (z : ι → E)
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z + b • s.centerMass w₂ z =
    s.centerMass (fun i => a * w₁ i + b * w₂ i) z := by
  have hw : (∑ i ∈ s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

theorem Finset.centerMass_ite_eq [DecidableEq ι] (hi : i ∈ t) :
    t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i := by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j ∈ t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, if_pos hi]
  · rw [sum_ite_eq, if_pos hi]

variable {t}

theorem Finset.centerMass_subset {t' : Finset ι} (ht : t ⊆ t') (h : ∀ i ∈ t', i ∉ t → w i = 0) :
    t.centerMass w z = t'.centerMass w z := by
  rw [centerMass, sum_subset ht h, smul_sum, centerMass, smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit, zero_smul, smul_zero]

theorem Finset.centerMass_filter_ne_zero [∀ i, Decidable (w i ≠ 0)] :
    {i ∈ t | w i ≠ 0}.centerMass w z = t.centerMass w z :=
  Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and, Ne, Classical.not_not] using hit'

namespace Finset

variable [LinearOrder R] [IsOrderedAddMonoid α] [PosSMulMono R α]

theorem centerMass_le_sup {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.centerMass w f ≤ s.sup' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f := by
  rw [centerMass, inv_smul_le_iff_of_pos hw₁, sum_smul]
  exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) <| hw₀ i hi

set_option backward.isDefEq.respectTransparency false in
theorem inf_le_centerMass {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.inf' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f ≤ s.centerMass w f :=
  centerMass_le_sup (α := αᵒᵈ) hw₀ hw₁

end Finset

variable {z}

lemma Finset.centerMass_const (hw : ∑ j ∈ t, w j ≠ 0) (c : E) :
    t.centerMass w (Function.const _ c) = c := by
  simp [centerMass, ← sum_smul, hw]

lemma Finset.centerMass_congr [DecidableEq ι] {t' : Finset ι} {w' : ι → R} {z' : ι → E}
    (h : ∀ i, (i ∈ t ∧ w i ≠ 0 ∨ i ∈ t' ∧ w' i ≠ 0) → i ∈ t ∩ t' ∧ w i = w' i ∧ z i = z' i) :
    t.centerMass w z = t'.centerMass w' z' := by
  classical
  rw [← centerMass_filter_ne_zero, centerMass, ← centerMass_filter_ne_zero, centerMass]
  congr 1
  · congr 1
    exact sum_congr (by grind) (by grind)
  · exact sum_congr (by grind) (by grind)

lemma Finset.centerMass_congr_finset [DecidableEq ι] {t' : Finset ι}
    (h : ∀ i ∈ t ∪ t', w i ≠ 0 → i ∈ t ∩ t') : t.centerMass w z = t'.centerMass w z :=
  centerMass_congr (by grind)

lemma Finset.centerMass_congr_weights {w' : ι → R} (h : ∀ i ∈ t, w i = w' i) :
    t.centerMass w z = t.centerMass w' z := by
  classical
  exact centerMass_congr (by grind)

lemma Finset.centerMass_congr_fun {z' : ι → E} (h : ∀ i ∈ t, w i ≠ 0 → z i = z' i) :
    t.centerMass w z = t.centerMass w z' := by
  classical
  exact centerMass_congr (by grind)

lemma Finset.centerMass_of_sum_add_sum_eq_zero {s t : Finset ι}
    (hw : ∑ i ∈ s, w i + ∑ i ∈ t, w i = 0) (hz : ∑ i ∈ s, w i • z i + ∑ i ∈ t, w i • z i = 0) :
    s.centerMass w z = t.centerMass w z := by
  simp [centerMass, eq_neg_of_add_eq_zero_right hw, eq_neg_of_add_eq_zero_left hz]

variable [LinearOrder R] [IsStrictOrderedRing R] [IsOrderedAddMonoid α] [PosSMulMono R α]

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem Convex.centerMass_mem (hs : Convex R s) :
    (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i ∈ t, w i) → (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ hpos hmem
    have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
    have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
    rw [sum_insert hi] at hpos
    by_cases hsum_t : ∑ j ∈ t, w j = 0
    · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have wz : ∑ j ∈ t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
      simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
      simp only [hsum_t, add_zero] at hpos
      rw [← mul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
      exact zi
    · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
      refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      · intro j hj
        exact hmem j (mem_insert_of_mem hj)
      · exact h₀ _ (mem_insert_self _ _)

theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) : (∑ i ∈ t, w i • z i) ∈ s := by
  simpa only [h₁, centerMass, inv_one, one_smul] using
    hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

/-- A version of `Convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R` is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a module over `R` such
that `z i ∈ s` whenever `w i ≠ 0`, then the sum `∑ᶠ i, w i • z i` belongs to `s`. See also
`PartitionOfUnity.finsum_smul_mem_convex`. -/
theorem Convex.finsum_mem {ι : Sort*} {w : ι → R} {z : ι → E} {s : Set E} (hs : Convex R s)
    (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ s) :
    (∑ᶠ i, w i • z i) ∈ s := by
  have hfin_w : HasFiniteSupport (w ∘ PLift.down) := by
    by_contra H
    rw [finsum, dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) ⊆ hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dif_pos hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi

theorem convex_iff_sum_mem : Convex R s ↔ ∀ (t : Finset E) (w : E → R),
    (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ x ∈ t, x ∈ s) → (∑ x ∈ t, w x • x) ∈ s := by
  classical
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert h {x, y} (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
    · grind
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption

theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
    t.centerMass w z ∈ convexHull R s :=
  (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s <| hz i hi

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
lemma Finset.centerMass_mem_convexHull_of_nonpos (t : Finset ι) (hw₀ : ∀ i ∈ t, w i ≤ 0)
    (hws : ∑ i ∈ t, w i < 0) (hz : ∀ i ∈ t, z i ∈ s) : t.centerMass w z ∈ convexHull R s := by
  rw [← centerMass_neg_left]
  exact Finset.centerMass_mem_convexHull _ (fun _i hi ↦ neg_nonneg.2 <| hw₀ _ hi) (by simpa) hz

/-- A refinement of `Finset.centerMass_mem_convexHull` when the indexed family is a `Finset` of
the space. -/
theorem Finset.centerMass_id_mem_convexHull (t : Finset E) {w : E → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) : t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
lemma Finset.centerMass_id_mem_convexHull_of_nonpos (t : Finset E) {w : E → R}
    (hw₀ : ∀ i ∈ t, w i ≤ 0) (hws : ∑ i ∈ t, w i < 0) :
    t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ ↦ mem_coe.2

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι → E} {w : ι → R}
    (hw₂ : ∑ i ∈ t, w i = 1) : t.affineCombination R p w = centerMass t w p := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_zero, t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]

theorem affineCombination_mem_convexHull {s : Finset ι} {v : ι → E} {w : ι → R}
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1) :
    s.affineCombination R v w ∈ convexHull R (range v) := by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp

/-- The centroid can be regarded as a center of mass. -/
@[simp]
theorem Finset.centroid_eq_centerMass (s : Finset ι) (hs : s.Nonempty) (p : ι → E) :
    s.centroid R p = s.centerMass (s.centroidWeights R) p :=
  affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)

theorem Finset.centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) :
    s.centroid R id ∈ convexHull R (s : Set E) := by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
  · have hs_card : (#s : R) ≠ 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀, Ne, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]

theorem convexHull_range_eq_exists_affineCombination (v : ι → E) : convexHull R (range v) =
    { x | ∃ (s : Finset ι) (w : ι → R), (∀ i ∈ s, 0 ≤ w i) ∧ s.sum w = 1 ∧
      s.affineCombination R v w = x } := by
  classical
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    exact ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι → R := fun i => (if i ∈ s then a * w i else 0) + if i ∈ s' then b * w' i else 0
    have hW₁ : (s ∪ s').sum W = 1 := by
      rw [sum_add_distrib, ← sum_subset subset_union_left,
        ← sum_subset subset_union_right, sum_ite_of_true,
        sum_ite_of_true, ← mul_sum, ← mul_sum, hw₁, hw₁', ← add_mul, hab,
        mul_one] <;> intros <;> simp_all
    refine ⟨s ∪ s', W, ?_, hW₁, ?_⟩
    · rintro i -
      by_cases hi : i ∈ s <;> by_cases hi' : i ∈ s' <;>
        simp [W, hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
    · simp_rw [W, affineCombination_eq_linear_combination (s ∪ s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset subset_union_left, ← sum_subset subset_union_right]
      · simp only [ite_smul, sum_ite_of_true fun _ hi => hi, mul_smul, ← smul_sum]
      · intro i _ hi'
        simp [hi']
      · intro i _ hi'
        simp [hi']
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affineCombination_mem_convexHull hw₀ hw₁

/--
Convex hull of `s` is equal to the set of all centers of masses of `Finset`s `t`, `z '' t ⊆ s`.
For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use convexity of the convex hull instead.
-/
theorem convexHull_eq (s : Set E) : convexHull R s =
    { x : E | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E), (∀ i ∈ t, 0 ≤ w i) ∧
      ∑ i ∈ t, w i = 1 ∧ (∀ i ∈ t, z i ∈ s) ∧ t.centerMass w z = x } := by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, sum_singleton _ _,
      fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, _, _, _, ?_, ?_, ?_, rfl⟩
    · rintro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
        apply_rules [mul_nonneg, hwx₀, hwy₀]
    · simp [← mul_sum, *]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz

/-- Universe polymorphic version of the reverse implication of `mem_convexHull_iff_exists_fintype`.
-/
lemma mem_convexHull_of_exists_fintype {s : Set E} {x : E} [Fintype ι] (w : ι → R) (z : ι → E)
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hz : ∀ i, z i ∈ s) (hx : ∑ i, w i • z i = x) :
    x ∈ convexHull R s := by
  rw [← hx, ← centerMass_eq_of_sum_1 _ _ hw₁]
  exact centerMass_mem_convexHull _ (by simpa using hw₀) (by simp [hw₁]) (by simpa using hz)

/-- The convex hull of `s` is equal to the set of centers of masses of finite families of points in
`s`.

For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use `mem_convexHull_of_exists_fintype` of the convex hull instead. -/
lemma mem_convexHull_iff_exists_fintype {s : Set E} {x : E} :
    x ∈ convexHull R s ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → R) (z : ι → E), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x := by
  constructor
  · simp only [convexHull_eq, mem_setOf_eq]
    rintro ⟨ι, t, w, z, h⟩
    refine ⟨t, inferInstance, w ∘ (↑), z ∘ (↑), ?_⟩
    simpa [← sum_attach t, centerMass_eq_of_sum_1 _ _ h.2.1] using h
  · rintro ⟨ι, _, w, z, hw₀, hw₁, hz, hx⟩
    exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx

theorem Finset.convexHull_eq (s : Finset E) : convexHull R ↑s =
    { x : E | ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x } := by
  classical
  refine Set.Subset.antisymm (convexHull_min ?_ ?_) ?_
  · intro x hx
    rw [Finset.mem_coe] at hx
    refine ⟨_, ?_, ?_, Finset.centerMass_ite_eq _ _ _ hx⟩
    · intros
      split_ifs
      exacts [zero_le_one, le_refl 0]
    · rw [Finset.sum_ite_eq, if_pos hx]
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine ⟨_, ?_, ?_, rfl⟩
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
    · simp only [Finset.sum_add_distrib, ← mul_sum, mul_one, *]
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx

theorem Finset.mem_convexHull {s : Finset E} {x : E} : x ∈ convexHull R (s : Set E) ↔
    ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x := by
  rw [Finset.convexHull_eq, Set.mem_setOf_eq]

/-- This is a version of `Finset.mem_convexHull` stated without `Finset.centerMass`. -/
lemma Finset.mem_convexHull' {s : Finset E} {x : E} :
    x ∈ convexHull R (s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x := by
  rw [mem_convexHull]
  refine exists_congr fun w ↦ and_congr_right' <| and_congr_right fun hw ↦ ?_
  simp_rw [centerMass_eq_of_sum_1 _ _ hw, id_eq]

theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =
    { x : E | ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ hs.toFinset, w y = 1 ∧
      hs.toFinset.centerMass w id = x } := by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq

/-- A weak version of Carathéodory's theorem. -/
theorem convexHull_eq_union_convexHull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finset E) (_ : ↑t ⊆ s), convexHull R ↑t := by
  classical
  refine Subset.antisymm ?_ ?_
  · rw [_root_.convexHull_eq]
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    simp only [mem_iUnion]
    refine ⟨t.image z, ?_, ?_⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
    · apply t.centerMass_mem_convexHull hw₀
      · simp only [hw₁, zero_lt_one]
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono

/-- The `vectorSpan` of a segment is the span of the difference of its endpoints. -/
theorem vectorSpan_segment {p₁ p₂ : E} :
    vectorSpan R (segment R p₁ p₂) = R ∙ (p₂ -ᵥ p₁) := by
  rw [← convexHull_pair, ← direction_affineSpan, affineSpan_convexHull,
      direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub]

theorem mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x ∈ convexHull R s)
    (hy : y ∈ convexHull R t) : (x, y) ∈ convexHull R (s ×ˢ t) := by
  rw [mem_convexHull_iff_exists_fintype] at hx hy ⊢
  obtain ⟨ι, _, w, f, hw₀, hw₁, hfs, hf⟩ := hx
  obtain ⟨κ, _, v, g, hv₀, hv₁, hgt, hg⟩ := hy
  have h_sum : ∑ i : ι × κ, w i.1 * v i.2 = 1 := by
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hw₁, hv₁, mul_one]
  refine ⟨ι × κ, inferInstance, fun p => w p.1 * v p.2, fun p ↦ (f p.1, g p.2),
    fun p ↦ mul_nonneg (hw₀ _) (hv₀ _), h_sum, fun p ↦ ⟨hfs _, hgt _⟩, ?_⟩
  ext
  · simp_rw [Prod.fst_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_comm (w _), mul_smul,
      sum_comm (γ := ι), ← Fintype.sum_smul_sum, hv₁, one_smul, hf]
  · simp_rw [Prod.snd_sum, Prod.smul_mk, Fintype.sum_prod_type, mul_smul, ← Fintype.sum_smul_sum,
      hw₁, one_smul, hg]

@[simp]
theorem convexHull_prod (s : Set E) (t : Set F) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t :=
  Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
        (convex_convexHull _ _).prod <| convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx

theorem convexHull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + convexHull R t := by
  simp_rw [← add_image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull, convexHull_prod]

variable (R E)

/-- `convexHull` is an additive monoid morphism under pointwise addition. -/
@[simps]
noncomputable def convexHullAddMonoidHom : Set E →+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero

variable {R E}

theorem convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]

theorem convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| convexHull R).sum :=
  map_list_sum (convexHullAddMonoidHom R E) l

theorem convexHull_multiset_sum (s : Multiset (Set E)) :
    convexHull R s.sum = (s.map <| convexHull R).sum :=
  map_multiset_sum (convexHullAddMonoidHom R E) s

theorem convexHull_sum {ι} (s : Finset ι) (t : ι → Set E) :
    convexHull R (∑ i ∈ s, t i) = ∑ i ∈ s, convexHull R (t i) :=
  map_sum (convexHullAddMonoidHom R E) _ _

/-- The convex hull of an affine basis is the intersection of the half-spaces defined by the
corresponding barycentric coordinates. -/
theorem AffineBasis.convexHull_eq_nonneg_coord {ι : Type*} (b : AffineBasis ι R E) :
    convexHull R (range b) = { x | ∀ i, 0 ≤ b.coord i x } := by
  rw [convexHull_range_eq_exists_affineCombination]
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi : i ∈ s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
    · rw [b.coord_apply_combination_of_notMem hi hw₁]
  · have hx' : x ∈ affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx

variable {s t t₁ t₂ : Finset E}

/-- Two simplices glue nicely if the union of their vertices is affine independent. -/
lemma AffineIndependent.convexHull_inter (hs : AffineIndependent R ((↑) : s → E))
    (ht₁ : t₁ ⊆ s) (ht₂ : t₂ ⊆ s) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ := by
  classical
  refine (Set.subset_inter (convexHull_mono inf_le_left) <|
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x ∈ t₁ then w₁ x else 0) - if x ∈ t₂ then w₂ x else 0
  have h₁w : ∑ i ∈ s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
  replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w <| by
    simp only [w, sub_smul, zero_smul, ite_smul, Finset.sum_sub_distrib, ← Finset.sum_filter, h₃w₁,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht₁, Finset.inter_eq_right.2 ht₂, h₃w₂,
      sub_self]
  have ht (x) (hx₁ : x ∈ t₁) (hx₂ : x ∉ t₂) : w₁ x = 0 := by
    simpa [w, hx₁, hx₂] using hs _ (ht₁ hx₁)
  refine ⟨w₁, ?_, ?_, ?_⟩
  · simp only [and_imp, Finset.mem_inter]
    exact fun y hy₁ _ ↦ h₁w₁ y hy₁
  all_goals
  · rwa [sum_subset inter_subset_left]
    rintro x
    simp_intro hx₁ hx₂
    simp [ht x hx₁ hx₂]

/-- Two simplices glue nicely if the union of their vertices is affine independent.

Note that `AffineIndependent.convexHull_inter` should be more versatile in most use cases. -/
lemma AffineIndependent.convexHull_inter' [DecidableEq E]
    (hs : AffineIndependent R ((↑) : ↑(t₁ ∪ t₂) → E)) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ :=
  hs.convexHull_inter subset_union_left subset_union_right

end

section pi
variable {𝕜 ι : Type*} {E : ι → Type*} [Finite ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Π i, AddCommGroup (E i)] [Π i, Module 𝕜 (E i)] {s : Set ι} {t : Π i, Set (E i)} {x : Π i, E i}

open Finset Fintype

lemma mem_convexHull_pi (h : ∀ i ∈ s, x i ∈ convexHull 𝕜 (t i)) : x ∈ convexHull 𝕜 (s.pi t) := by
  classical
  cases nonempty_fintype ι
  wlog hs : s = Set.univ generalizing s t
  · rw [← pi_univ_ite]
    refine this (fun i _ ↦ ?_) rfl
    split_ifs with hi
    · exact h i hi
    · simp
  subst hs
  simp only [Set.mem_univ, mem_convexHull_iff_exists_fintype, true_implies] at h
  choose κ _ w f hw₀ hw₁ hft hf using h
  refine mem_convexHull_of_exists_fintype (fun k : Π i, κ i ↦ ∏ i, w i (k i)) (fun g i ↦ f _ (g i))
    (fun g ↦ prod_nonneg fun _ _ ↦ hw₀ _ _) ?_ (fun _ _ _ ↦ hft _ _) ?_
  · rw [← Fintype.prod_sum]
    exact prod_eq_one fun _ _ ↦ hw₁ _
  ext i
  calc
    _ = ∑ g : ∀ i, κ i, (∏ i, w i (g i)) • f i (g i) := by
      simp only [Finset.sum_apply, Pi.smul_apply]
    _ = ∑ j : κ i, ∑ g : {g : ∀ k, κ k // g i = j},
          (∏ k, w k (g.1 k)) • f i ((g : ∀ i, κ i) i) := by
      rw [← Fintype.sum_fiberwise fun g : ∀ k, κ k ↦ g i]
    _ = ∑ j : κ i, (∑ g : {g : ∀ k, κ k // g i = j}, ∏ k, w k (g.1 k)) • f i j := by
      simp_rw [sum_smul]
      congr! with j _ g _
      exact g.2
    _ = ∑ j : κ i, w i j • f i j := ?_
    _ = x i := hf _
  congr! with j _
  calc
    ∑ g : {g : ∀ k, κ k // g i = j}, ∏ k, w k (g.1 k)
      = ∑ g ∈ piFinset fun k ↦ if hk : k = i then hk ▸ {j} else univ, ∏ k, w k (g k) :=
      Finset.sum_bij' (fun g _ ↦ g) (fun g hg ↦ ⟨g, by simpa using mem_piFinset.1 hg i⟩)
        (by aesop) (by simp) (by simp) (by simp) (by simp)
    _ = w i j := by
      rw [← prod_univ_sum, ← prod_mul_prod_compl, Finset.prod_singleton, Finset.sum_eq_single,
        Finset.prod_eq_one, mul_one] <;> simp +contextual [hw₁]

@[simp] lemma convexHull_pi (s : Set ι) (t : Π i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi (fun i ↦ convexHull 𝕜 (t i)) :=
  Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ ↦ subset_convexHull _ _) <| convex_pi <|
    fun _ _ ↦ convex_convexHull _ _) fun _ ↦ mem_convexHull_pi

end pi

namespace Affine.Simplex

/-- The closed interior of a simplex is the convex hull of all vertices. -/
@[simp] theorem convexHull_eq_closedInterior {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {n : ℕ} (s : Simplex 𝕜 V n) :
    convexHull 𝕜 (Set.range s.points) = s.closedInterior := by
  ext p
  rw [convexHull_range_eq_exists_affineCombination, Set.mem_setOf]
  constructor <;> intro h
  · obtain ⟨u, w, hw, hw1, rfl⟩ := h
    have hw' : ∀ i ∈ u, w i ≤ 1 := by
      intro i hi
      rw [← hw1]
      apply Finset.single_le_sum (fun j hj ↦ hw j hj) hi
    have hw1' : ∑ i, (u : Set (Fin (n + 1))).indicator w i = 1 := by
      simpa [Finset.sum_indicator_subset _ u.subset_univ] using hw1
    rw [Finset.affineCombination_indicator_subset _ _ u.subset_univ,
      affineCombination_mem_closedInterior_iff hw1']
    intro i
    by_cases hi : i ∈ (u : Set (Fin (n + 1))) <;> aesop
  · obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
      Set.mem_of_mem_of_subset h s.closedInterior_subset_affineSpan
    rw [affineCombination_mem_closedInterior_iff hw1] at h
    exact ⟨Finset.univ, w, fun i _ ↦ (h i).1, hw1, rfl⟩

end Affine.Simplex

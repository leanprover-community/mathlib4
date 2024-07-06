/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Basis

#align_import analysis.convex.combination from "leanprover-community/mathlib"@"92bd7b1ffeb306a89f450bee126ddd8a284c259d"

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


open Set Function

open scoped Classical
open Pointwise

universe u u'

variable {R R' E F ι ι' α : Type*} [LinearOrderedField R] [LinearOrderedField R'] [AddCommGroup E]
  [AddCommGroup F] [LinearOrderedAddCommGroup α] [Module R E] [Module R F] [Module R α]
  [OrderedSMul R α] {s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i ∈ t, w i)⁻¹ • ∑ i ∈ t, w i • z i
#align finset.center_mass Finset.centerMass

variable (i j : ι) (c : R) (t : Finset ι) (w : ι → R) (z : ι → E)

open Finset

theorem Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0 := by
  simp only [centerMass, sum_empty, smul_zero]
#align finset.center_mass_empty Finset.centerMass_empty

theorem Finset.centerMass_pair (hne : i ≠ j) :
    ({i, j} : Finset ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [centerMass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]
#align finset.center_mass_pair Finset.centerMass_pair

variable {w}

theorem Finset.centerMass_insert (ha : i ∉ t) (hw : ∑ j ∈ t, w j ≠ 0) :
    (insert i t).centerMass w z =
      (w i / (w i + ∑ j ∈ t, w j)) • z i +
        ((∑ j ∈ t, w j) / (w i + ∑ j ∈ t, w j)) • t.centerMass w z := by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]
#align finset.center_mass_insert Finset.centerMass_insert

theorem Finset.centerMass_singleton (hw : w i ≠ 0) : ({i} : Finset ι).centerMass w z = z i := by
  rw [centerMass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]
#align finset.center_mass_singleton Finset.centerMass_singleton

@[simp] lemma Finset.centerMass_neg_left : t.centerMass (-w) z = t.centerMass w z := by
  simp [centerMass, inv_neg]

lemma Finset.centerMass_smul_left {c : R'} [Module R' R] [Module R' E] [SMulCommClass R' R R]
    [IsScalarTower R' R R] [SMulCommClass R R' E] [IsScalarTower R' R E] (hc : c ≠ 0) :
    t.centerMass (c • w) z = t.centerMass w z := by
  simp [centerMass, -smul_assoc, smul_assoc c, ← smul_sum, smul_inv₀, smul_smul_smul_comm, hc]

theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i ∈ t, w i = 1) :
    t.centerMass w z = ∑ i ∈ t, w i • z i := by
  simp only [Finset.centerMass, hw, inv_one, one_smul]
#align finset.center_mass_eq_of_sum_1 Finset.centerMass_eq_of_sum_1

theorem Finset.centerMass_smul : (t.centerMass w fun i => c • z i) = c • t.centerMass w z := by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]
#align finset.center_mass_smul Finset.centerMass_smul

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι → R) (zs : ι → E)
    (wt : ι' → R) (zt : ι' → E) (hws : ∑ i ∈ s, ws i = 1) (hwt : ∑ i ∈ t, wt i = 1) (a b : R)
    (hab : a + b = 1) : a • s.centerMass ws zs + b • t.centerMass wt zt = (s.disjSum t).centerMass
    (Sum.elim (fun i => a * ws i) fun j => b * wt j) (Sum.elim zs zt) := by
  rw [s.centerMass_eq_of_sum_1 _ hws, t.centerMass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ←
    Finset.sum_sum_elim, Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
  · rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]
#align finset.center_mass_segment' Finset.centerMass_segment'

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι → R) (z : ι → E)
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z + b • s.centerMass w₂ z =
    s.centerMass (fun i => a * w₁ i + b * w₂ i) z := by
  have hw : (∑ i ∈ s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [← mul_sum, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, Finset.centerMass_eq_of_sum_1 _ _ hw,
    smul_sum, sum_add_distrib, add_smul, mul_smul, *]
#align finset.center_mass_segment Finset.centerMass_segment

theorem Finset.centerMass_ite_eq (hi : i ∈ t) :
    t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i := by
  rw [Finset.centerMass_eq_of_sum_1]
  · trans ∑ j ∈ t, if i = j then z i else 0
    · congr with i
      split_ifs with h
      exacts [h ▸ one_smul _ _, zero_smul _ _]
    · rw [sum_ite_eq, if_pos hi]
  · rw [sum_ite_eq, if_pos hi]
#align finset.center_mass_ite_eq Finset.centerMass_ite_eq

variable {t}

theorem Finset.centerMass_subset {t' : Finset ι} (ht : t ⊆ t') (h : ∀ i ∈ t', i ∉ t → w i = 0) :
    t.centerMass w z = t'.centerMass w z := by
  rw [centerMass, sum_subset ht h, smul_sum, centerMass, smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit, zero_smul, smul_zero]
#align finset.center_mass_subset Finset.centerMass_subset

theorem Finset.centerMass_filter_ne_zero :
    (t.filter fun i => w i ≠ 0).centerMass w z = t.centerMass w z :=
  Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and_iff, Ne, Classical.not_not] using hit'
#align finset.center_mass_filter_ne_zero Finset.centerMass_filter_ne_zero

namespace Finset

theorem centerMass_le_sup {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.centerMass w f ≤ s.sup' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f := by
  rw [centerMass, inv_smul_le_iff_of_pos hw₁, sum_smul]
  exact sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (le_sup' _ hi) <| hw₀ i hi
#align finset.center_mass_le_sup Finset.centerMass_le_sup

theorem inf_le_centerMass {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i ∈ s, w i) :
    s.inf' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f ≤ s.centerMass w f :=
  @centerMass_le_sup R _ αᵒᵈ _ _ _ _ _ _ _ hw₀ hw₁
#align finset.inf_le_center_mass Finset.inf_le_centerMass

end Finset

variable {z}

lemma Finset.centerMass_of_sum_add_sum_eq_zero {s t : Finset ι}
    (hw : ∑ i ∈ s, w i + ∑ i ∈ t, w i = 0) (hz : ∑ i ∈ s, w i • z i + ∑ i ∈ t, w i • z i = 0) :
    s.centerMass w z = t.centerMass w z := by
  simp [centerMass, eq_neg_of_add_eq_zero_right hw, eq_neg_of_add_eq_zero_left hz, ← neg_inv]

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem Convex.centerMass_mem (hs : Convex R s) :
    (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i ∈ t, w i) → (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ s := by
  induction' t using Finset.induction with i t hi ht
  · simp [lt_irrefl]
  intro h₀ hpos hmem
  have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
  have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
  rw [sum_insert hi] at hpos
  by_cases hsum_t : ∑ j ∈ t, w j = 0
  · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
    have wz : ∑ j ∈ t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
    simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
    simp only [hsum_t, add_zero] at hpos
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul]
    exact zi
  · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
    refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
    · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
    · intro j hj
      exact hmem j (mem_insert_of_mem hj)
    · exact h₀ _ (mem_insert_self _ _)
#align convex.center_mass_mem Convex.centerMass_mem

theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) : (∑ i ∈ t, w i • z i) ∈ s := by
  simpa only [h₁, centerMass, inv_one, one_smul] using
    hs.centerMass_mem h₀ (h₁.symm ▸ zero_lt_one) hz
#align convex.sum_mem Convex.sum_mem

/-- A version of `Convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R` is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a module over `R` such
that `z i ∈ s` whenever `w i ≠ 0`, then the sum `∑ᶠ i, w i • z i` belongs to `s`. See also
`PartitionOfUnity.finsum_smul_mem_convex`. -/
theorem Convex.finsum_mem {ι : Sort*} {w : ι → R} {z : ι → E} {s : Set E} (hs : Convex R s)
    (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ s) :
    (∑ᶠ i, w i • z i) ∈ s := by
  have hfin_w : (support (w ∘ PLift.down)).Finite := by
    by_contra H
    rw [finsum, dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ PLift.down) ⊆ hfin_w.toFinset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_toFinset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine hs.sum_mem (fun _ _ => h₀ _) ?_ fun i hi => hz _ ?_
  · rwa [finsum, dif_pos hfin_w] at h₁
  · rwa [hfin_w.mem_toFinset] at hi
#align convex.finsum_mem Convex.finsum_mem

theorem convex_iff_sum_mem : Convex R s ↔ ∀ (t : Finset E) (w : E → R),
    (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ x ∈ t, x ∈ s) → (∑ x ∈ t, w x • x) ∈ s := by
  refine ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, ?_⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases : x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
  · convert h {x, y} (fun z => if z = y then b else a) _ _ _
    -- Porting note: Original proof had 2 `simp_intro i hi`
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
    · intro i _
      simp only
      split_ifs <;> assumption
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
    · intro i hi
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      cases hi <;> subst i <;> assumption
#align convex_iff_sum_mem convex_iff_sum_mem

theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i ∈ t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
    t.centerMass w z ∈ convexHull R s :=
  (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s <| hz i hi
#align finset.center_mass_mem_convex_hull Finset.centerMass_mem_convexHull

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
#align finset.center_mass_id_mem_convex_hull Finset.centerMass_id_mem_convexHull

/-- A version of `Finset.centerMass_mem_convexHull` for when the weights are nonpositive. -/
lemma Finset.centerMass_id_mem_convexHull_of_nonpos (t : Finset E) {w : E → R}
    (hw₀ : ∀ i ∈ t, w i ≤ 0) (hws : ∑ i ∈ t, w i < 0) :
    t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull_of_nonpos hw₀ hws fun _ ↦ mem_coe.2

theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι → E} {w : ι → R}
    (hw₂ : ∑ i ∈ t, w i = 1) : t.affineCombination R p w = centerMass t w p := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_zero, t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]
#align affine_combination_eq_center_mass affineCombination_eq_centerMass

theorem affineCombination_mem_convexHull {s : Finset ι} {v : ι → E} {w : ι → R}
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1) :
    s.affineCombination R v w ∈ convexHull R (range v) := by
  rw [affineCombination_eq_centerMass hw₁]
  apply s.centerMass_mem_convexHull hw₀
  · simp [hw₁]
  · simp
#align affine_combination_mem_convex_hull affineCombination_mem_convexHull

/-- The centroid can be regarded as a center of mass. -/
@[simp]
theorem Finset.centroid_eq_centerMass (s : Finset ι) (hs : s.Nonempty) (p : ι → E) :
    s.centroid R p = s.centerMass (s.centroidWeights R) p :=
  affineCombination_eq_centerMass (s.sum_centroidWeights_eq_one_of_nonempty R hs)
#align finset.centroid_eq_center_mass Finset.centroid_eq_centerMass

theorem Finset.centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) :
    s.centroid R id ∈ convexHull R (s : Set E) := by
  rw [s.centroid_eq_centerMass hs]
  apply s.centerMass_id_mem_convexHull
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
  · have hs_card : (s.card : R) ≠ 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel, Ne, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]
#align finset.centroid_mem_convex_hull Finset.centroid_mem_convexHull

theorem convexHull_range_eq_exists_affineCombination (v : ι → E) : convexHull R (range v) =
    { x | ∃ (s : Finset ι) (w : ι → R), (∀ i ∈ s, 0 ≤ w i) ∧ s.sum w = 1 ∧
      s.affineCombination R v w = x } := by
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
    · simp_rw [affineCombination_eq_linear_combination (s ∪ s') v _ hW₁,
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
#align convex_hull_range_eq_exists_affine_combination convexHull_range_eq_exists_affineCombination

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
    · simp [Finset.sum_sum_elim, ← mul_sum, *]
    · intro i hi
      rw [Finset.mem_disjSum] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz
#align convex_hull_eq convexHull_eq

theorem Finset.convexHull_eq (s : Finset E) : convexHull R ↑s =
    { x : E | ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x } := by
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
#align finset.convex_hull_eq Finset.convexHull_eq

theorem Finset.mem_convexHull {s : Finset E} {x : E} : x ∈ convexHull R (s : Set E) ↔
    ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ s.centerMass w id = x := by
  rw [Finset.convexHull_eq, Set.mem_setOf_eq]
#align finset.mem_convex_hull Finset.mem_convexHull

/-- This is a version of `Finset.mem_convexHull` stated without `Finset.centerMass`. -/
lemma Finset.mem_convexHull' {s : Finset E} {x : E} :
    x ∈ convexHull R (s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x := by
  rw [mem_convexHull]
  refine exists_congr fun w ↦ and_congr_right' $ and_congr_right fun hw ↦ ?_
  simp_rw [centerMass_eq_of_sum_1 _ _ hw, id_eq]

theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =
    { x : E | ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ hs.toFinset, w y = 1 ∧
      hs.toFinset.centerMass w id = x } := by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq
#align set.finite.convex_hull_eq Set.Finite.convexHull_eq

/-- A weak version of Carathéodory's theorem. -/
theorem convexHull_eq_union_convexHull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finset E) (w : ↑t ⊆ s), convexHull R ↑t := by
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
#align convex_hull_eq_union_convex_hull_finite_subsets convexHull_eq_union_convexHull_finite_subsets

theorem mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x ∈ convexHull R s)
    (hy : y ∈ convexHull R t) : (x, y) ∈ convexHull R (s ×ˢ t) := by
  rw [_root_.convexHull_eq] at hx hy ⊢
  obtain ⟨ι, a, w, S, hw, hw', hS, hSp⟩ := hx
  obtain ⟨κ, b, v, T, hv, hv', hT, hTp⟩ := hy
  have h_sum : ∑ i ∈ a ×ˢ b, w i.fst * v i.snd = 1 := by
    rw [Finset.sum_product, ← hw']
    congr
    ext i
    have : ∑ y ∈ b, w i * v y = ∑ y ∈ b, v y * w i := by
      congr
      ext
      simp [mul_comm]
    rw [this, ← Finset.sum_mul, hv']
    simp
  refine
    ⟨ι × κ, a ×ˢ b, fun p => w p.1 * v p.2, fun p => (S p.1, T p.2), fun p hp => ?_, h_sum,
      fun p hp => ?_, ?_⟩
  · rw [mem_product] at hp
    exact mul_nonneg (hw p.1 hp.1) (hv p.2 hp.2)
  · rw [mem_product] at hp
    exact ⟨hS p.1 hp.1, hT p.2 hp.2⟩
  ext
  · rw [← hSp, Finset.centerMass_eq_of_sum_1 _ _ hw', Finset.centerMass_eq_of_sum_1 _ _ h_sum]
    simp_rw [Prod.fst_sum, Prod.smul_mk]
    rw [Finset.sum_product]
    congr
    ext i
    have : (∑ j ∈ b, (w i * v j) • S i) = ∑ j ∈ b, v j • w i • S i := by
      congr
      ext
      rw [mul_smul, smul_comm]
    rw [this, ← Finset.sum_smul, hv', one_smul]
  · rw [← hTp, Finset.centerMass_eq_of_sum_1 _ _ hv', Finset.centerMass_eq_of_sum_1 _ _ h_sum]
    simp_rw [Prod.snd_sum, Prod.smul_mk]
    rw [Finset.sum_product, Finset.sum_comm]
    congr
    ext j
    simp_rw [mul_smul]
    rw [← Finset.sum_smul, hw', one_smul]
#align mk_mem_convex_hull_prod mk_mem_convexHull_prod

@[simp]
theorem convexHull_prod (s : Set E) (t : Set F) :
    convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t :=
  Subset.antisymm
      (convexHull_min (prod_mono (subset_convexHull _ _) <| subset_convexHull _ _) <|
        (convex_convexHull _ _).prod <| convex_convexHull _ _) <|
    prod_subset_iff.2 fun _ hx _ => mk_mem_convexHull_prod hx
#align convex_hull_prod convexHull_prod

theorem convexHull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + convexHull R t := by
  simp_rw [← image2_add, ← image_prod, ← IsLinearMap.isLinearMap_add.image_convexHull,
    convexHull_prod]
#align convex_hull_add convexHull_add

variable (R E)

/-- `convexHull` is an additive monoid morphism under pointwise addition. -/
@[simps]
def convexHullAddMonoidHom : Set E →+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero
#align convex_hull_add_monoid_hom convexHullAddMonoidHom

variable {R E}

theorem convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convexHull_add, ← convexHull_neg]
#align convex_hull_sub convexHull_sub

theorem convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| convexHull R).sum :=
  map_list_sum (convexHullAddMonoidHom R E) l
#align convex_hull_list_sum convexHull_list_sum

theorem convexHull_multiset_sum (s : Multiset (Set E)) :
    convexHull R s.sum = (s.map <| convexHull R).sum :=
  map_multiset_sum (convexHullAddMonoidHom R E) s
#align convex_hull_multiset_sum convexHull_multiset_sum

theorem convexHull_sum {ι} (s : Finset ι) (t : ι → Set E) :
    convexHull R (∑ i ∈ s, t i) = ∑ i ∈ s, convexHull R (t i) :=
  map_sum (convexHullAddMonoidHom R E) _ _
#align convex_hull_sum convexHull_sum

/-! ### `stdSimplex` -/


variable (ι) [Fintype ι] {f : ι → R}

/-- `stdSimplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
theorem convexHull_basis_eq_stdSimplex :
    convexHull R (range fun i j : ι => if i = j then (1 : R) else 0) = stdSimplex R ι := by
  refine Subset.antisymm (convexHull_min ?_ (convex_stdSimplex R ι)) ?_
  · rintro _ ⟨i, rfl⟩
    exact ite_eq_mem_stdSimplex R i
  · rintro w ⟨hw₀, hw₁⟩
    rw [pi_eq_sum_univ w, ← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i) (hw₁.symm ▸ zero_lt_one)
      fun i _ => mem_range_self i
#align convex_hull_basis_eq_std_simplex convexHull_basis_eq_stdSimplex

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x ∈ s, w x • x`.

Since we have no sums over finite sets, we use sum over `@Finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
theorem Set.Finite.convexHull_eq_image {s : Set E} (hs : s.Finite) : convexHull R s =
    haveI := hs.fintype
    (⇑(∑ x : s, (@LinearMap.proj R s _ (fun _ => R) _ _ x).smulRight x.1)) '' stdSimplex R s := by
  letI := hs.fintype
  rw [← convexHull_basis_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  apply congr_arg
  simp_rw [Function.comp]
  convert Subtype.range_coe.symm
  simp [LinearMap.sum_apply, ite_smul, Finset.filter_eq, Finset.mem_univ]
#align set.finite.convex_hull_eq_image Set.Finite.convexHull_eq_image

/-- All values of a function `f ∈ stdSimplex 𝕜 ι` belong to `[0, 1]`. -/
theorem mem_Icc_of_mem_stdSimplex (hf : f ∈ stdSimplex R ι) (x) : f x ∈ Icc (0 : R) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩
#align mem_Icc_of_mem_std_simplex mem_Icc_of_mem_stdSimplex

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
    · rw [b.coord_apply_combination_of_not_mem hi hw₁]
  · have hx' : x ∈ affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    refine ⟨s, w, ?_, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx
#align affine_basis.convex_hull_eq_nonneg_coord AffineBasis.convexHull_eq_nonneg_coord

variable {s t t₁ t₂ : Finset E}

/-- Two simplices glue nicely if the union of their vertices is affine independent. -/
lemma AffineIndependent.convexHull_inter (hs : AffineIndependent R ((↑) : s → E))
    (ht₁ : t₁ ⊆ s) (ht₂ : t₂ ⊆ s) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ := by
  refine (Set.subset_inter (convexHull_mono inf_le_left) $
    convexHull_mono inf_le_right).antisymm ?_
  simp_rw [Set.subset_def, mem_inter_iff, Set.inf_eq_inter, ← coe_inter, mem_convexHull']
  rintro x ⟨⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩, w₂, -, h₂w₂, h₃w₂⟩
  let w (x : E) : R := (if x ∈ t₁ then w₁ x else 0) - if x ∈ t₂ then w₂ x else 0
  have h₁w : ∑ i ∈ s, w i = 0 := by simp [w, Finset.inter_eq_right.2, *]
  replace hs := hs.eq_zero_of_sum_eq_zero_subtype h₁w $ by
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
lemma AffineIndependent.convexHull_inter' (hs : AffineIndependent R ((↑) : ↑(t₁ ∪ t₂) → E)) :
    convexHull R (t₁ ∩ t₂ : Set E) = convexHull R t₁ ∩ convexHull R t₂ :=
  hs.convexHull_inter subset_union_left subset_union_right

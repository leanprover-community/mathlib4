/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov
-/
import Mathlib.Algebra.BigOperators.Order
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

open BigOperators Classical Pointwise

universe u u'

variable {R E F ι ι' α : Type*} [LinearOrderedField R] [AddCommGroup E] [AddCommGroup F]
  [LinearOrderedAddCommGroup α] [Module R E] [Module R F] [Module R α] [OrderedSMul R α] {s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i in t, w i)⁻¹ • ∑ i in t, w i • z i
#align finset.center_mass Finset.centerMass

variable (i j : ι) (c : R) (t : Finset ι) (w : ι → R) (z : ι → E)

open Finset

theorem Finset.centerMass_empty : (∅ : Finset ι).centerMass w z = 0 := by
  simp only [centerMass, sum_empty, smul_zero]
  -- 🎉 no goals
#align finset.center_mass_empty Finset.centerMass_empty

theorem Finset.centerMass_pair (hne : i ≠ j) :
    ({i, j} : Finset ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [centerMass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]
  -- 🎉 no goals
#align finset.center_mass_pair Finset.centerMass_pair

variable {w}

theorem Finset.centerMass_insert (ha : i ∉ t) (hw : ∑ j in t, w j ≠ 0) :
    (insert i t).centerMass w z =
      (w i / (w i + ∑ j in t, w j)) • z i +
        ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.centerMass w z := by
  simp only [centerMass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  -- ⊢ (w i / (w i + ∑ i in t, w i)) • z i + (w i + ∑ i in t, w i)⁻¹ • ∑ i in t, w  …
  congr 2
  -- ⊢ (w i + ∑ i in t, w i)⁻¹ = (∑ i in t, w i) / (w i + ∑ i in t, w i) * (∑ i in  …
  rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]
  -- 🎉 no goals
#align finset.center_mass_insert Finset.centerMass_insert

theorem Finset.centerMass_singleton (hw : w i ≠ 0) : ({i} : Finset ι).centerMass w z = z i := by
  rw [centerMass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]
  -- 🎉 no goals
#align finset.center_mass_singleton Finset.centerMass_singleton

theorem Finset.centerMass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) :
    t.centerMass w z = ∑ i in t, w i • z i := by
  simp only [Finset.centerMass, hw, inv_one, one_smul]
  -- 🎉 no goals
#align finset.center_mass_eq_of_sum_1 Finset.centerMass_eq_of_sum_1

theorem Finset.centerMass_smul : (t.centerMass w fun i => c • z i) = c • t.centerMass w z := by
  simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]
  -- 🎉 no goals
#align finset.center_mass_smul Finset.centerMass_smul

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem Finset.centerMass_segment' (s : Finset ι) (t : Finset ι') (ws : ι → R) (zs : ι → E)
    (wt : ι' → R) (zt : ι' → E) (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : R)
    (hab : a + b = 1) : a • s.centerMass ws zs + b • t.centerMass wt zt = (s.disjSum t).centerMass
    (Sum.elim (fun i => a * ws i) fun j => b * wt j) (Sum.elim zs zt) := by
  rw [s.centerMass_eq_of_sum_1 _ hws, t.centerMass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ←
    Finset.sum_sum_elim, Finset.centerMass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
    -- ⊢ Sum.elim (fun x => a • ws x • zs x) (fun x => b • wt x • zt x) (Sum.inl val✝ …
                      -- 🎉 no goals
                      -- 🎉 no goals
  · rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab]
    -- 🎉 no goals
#align finset.center_mass_segment' Finset.centerMass_segment'

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem Finset.centerMass_segment (s : Finset ι) (w₁ w₂ : ι → R) (z : ι → E)
    (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z + b • s.centerMass w₂ z =
    s.centerMass (fun i => a * w₁ i + b * w₂ i) z := by
  have hw : (∑ i in s, (a * w₁ i + b * w₂ i)) = 1 := by
    simp only [mul_sum.symm, sum_add_distrib, mul_one, *]
  simp only [Finset.centerMass_eq_of_sum_1, Finset.centerMass_eq_of_sum_1 _ _ hw,
    smul_sum, sum_add_distrib, add_smul, mul_smul, *]
#align finset.center_mass_segment Finset.centerMass_segment

theorem Finset.centerMass_ite_eq (hi : i ∈ t) :
    t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i := by
  rw [Finset.centerMass_eq_of_sum_1]
  -- ⊢ ∑ i_1 in t, (if i = i_1 then 1 else 0) • z i_1 = z i
  trans ∑ j in t, if i = j then z i else 0
  · congr with i
    -- ⊢ (if i✝ = i then 1 else 0) • z i = if i✝ = i then z i✝ else 0
    split_ifs with h
    -- ⊢ 1 • z i = z i✝
    exacts [h ▸ one_smul _ _, zero_smul _ _]
    -- 🎉 no goals
  · rw [sum_ite_eq, if_pos hi]
    -- 🎉 no goals
  · rw [sum_ite_eq, if_pos hi]
    -- 🎉 no goals
#align finset.center_mass_ite_eq Finset.centerMass_ite_eq

variable {t}

theorem Finset.centerMass_subset {t' : Finset ι} (ht : t ⊆ t') (h : ∀ i ∈ t', i ∉ t → w i = 0) :
    t.centerMass w z = t'.centerMass w z := by
  rw [centerMass, sum_subset ht h, smul_sum, centerMass, smul_sum]
  -- ⊢ ∑ x in t, (∑ x in t', w x)⁻¹ • w x • z x = ∑ x in t', (∑ i in t', w i)⁻¹ • w …
  apply sum_subset ht
  -- ⊢ ∀ (x : ι), x ∈ t' → ¬x ∈ t → (∑ x in t', w x)⁻¹ • w x • z x = 0
  intro i hit' hit
  -- ⊢ (∑ x in t', w x)⁻¹ • w i • z i = 0
  rw [h i hit' hit, zero_smul, smul_zero]
  -- 🎉 no goals
#align finset.center_mass_subset Finset.centerMass_subset

theorem Finset.centerMass_filter_ne_zero :
    (t.filter fun i => w i ≠ 0).centerMass w z = t.centerMass w z :=
  Finset.centerMass_subset z (filter_subset _ _) fun i hit hit' => by
    simpa only [hit, mem_filter, true_and_iff, Ne.def, Classical.not_not] using hit'
    -- 🎉 no goals
#align finset.center_mass_filter_ne_zero Finset.centerMass_filter_ne_zero

namespace Finset

theorem centerMass_le_sup {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i in s, w i) :
    s.centerMass w f ≤ s.sup' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f := by
                                                          -- ⊢ False
                                                                      -- 🎉 no goals
  rw [centerMass, inv_smul_le_iff hw₁, sum_smul]
  -- ⊢ ∑ i in s, w i • f i ≤ ∑ i in s, w i • sup' s (_ : Finset.Nonempty s) f
  exact sum_le_sum fun i hi => smul_le_smul_of_nonneg (le_sup' _ hi) <| hw₀ i hi
  -- 🎉 no goals
#align finset.center_mass_le_sup Finset.centerMass_le_sup

theorem inf_le_centerMass {s : Finset ι} {f : ι → α} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : 0 < ∑ i in s, w i) :
    s.inf' (nonempty_of_ne_empty <| by rintro rfl; simp at hw₁) f ≤ s.centerMass w f :=
                                       -- ⊢ False
                                                   -- 🎉 no goals
  @centerMass_le_sup R _ αᵒᵈ _ _ _ _ _ _ _ hw₀ hw₁
#align finset.inf_le_center_mass Finset.inf_le_centerMass

end Finset

variable {z}

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem Convex.centerMass_mem (hs : Convex R s) :
    (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i in t, w i) → (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ s := by
  induction' t using Finset.induction with i t hi ht
  -- ⊢ (∀ (i : ι), i ∈ ∅ → 0 ≤ w i) → 0 < ∑ i in ∅, w i → (∀ (i : ι), i ∈ ∅ → z i ∈ …
  · simp [lt_irrefl]
    -- 🎉 no goals
  intro h₀ hpos hmem
  -- ⊢ centerMass (insert i t) w z ∈ s
  have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
  -- ⊢ centerMass (insert i t) w z ∈ s
  have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
  -- ⊢ centerMass (insert i t) w z ∈ s
  rw [sum_insert hi] at hpos
  -- ⊢ centerMass (insert i t) w z ∈ s
  by_cases hsum_t : ∑ j in t, w j = 0
  -- ⊢ centerMass (insert i t) w z ∈ s
  · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
    -- ⊢ centerMass (insert i t) w z ∈ s
    have wz : ∑ j in t, w j • z j = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
    -- ⊢ centerMass (insert i t) w z ∈ s
    simp only [centerMass, sum_insert hi, wz, hsum_t, add_zero]
    -- ⊢ (w i)⁻¹ • w i • z i ∈ s
    simp only [hsum_t, add_zero] at hpos
    -- ⊢ (w i)⁻¹ • w i • z i ∈ s
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul]
    -- ⊢ z i ∈ s
    exact zi
    -- 🎉 no goals
  · rw [Finset.centerMass_insert _ _ _ hi hsum_t]
    -- ⊢ (w i / (w i + ∑ j in t, w j)) • z i + ((∑ j in t, w j) / (w i + ∑ j in t, w  …
    refine' convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos
    · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)
      -- 🎉 no goals
    · intro j hj
      -- ⊢ z j ∈ s
      exact hmem j (mem_insert_of_mem hj)
      -- 🎉 no goals
    · exact h₀ _ (mem_insert_self _ _)
      -- 🎉 no goals
#align convex.center_mass_mem Convex.centerMass_mem

theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) : (∑ i in t, w i • z i) ∈ s := by
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
  rw [finsum_eq_sum_pLift_of_support_subset hsub]
  -- ⊢ ∑ i in Finite.toFinset hfin_w, w i.down • z i.down ∈ s
  refine' hs.sum_mem (fun _ _ => h₀ _) _ fun i hi => hz _ _
  -- ⊢ ∑ i in Finite.toFinset hfin_w, w i.down = 1
  · rwa [finsum, dif_pos hfin_w] at h₁
    -- 🎉 no goals
  · rwa [hfin_w.mem_toFinset] at hi
    -- 🎉 no goals
#align convex.finsum_mem Convex.finsum_mem

theorem convex_iff_sum_mem : Convex R s ↔ ∀ (t : Finset E) (w : E → R),
    (∀ i ∈ t, 0 ≤ w i) → ∑ i in t, w i = 1 → (∀ x ∈ t, x ∈ s) → (∑ x in t, w x • x) ∈ s := by
  refine' ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, _⟩
  -- ⊢ (∀ (t : Finset E) (w : E → R), (∀ (i : E), i ∈ t → 0 ≤ w i) → ∑ i in t, w i  …
  intro h x hx y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ s
  by_cases h_cases : x = y
  -- ⊢ a • x + b • y ∈ s
  · rw [h_cases, ← add_smul, hab, one_smul]
    -- ⊢ y ∈ s
    exact hy
    -- 🎉 no goals
  · convert h {x, y} (fun z => if z = y then b else a) _ _ _
    -- Porting note: Original proof had 2 `simp_intro i hi`
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial]
      -- 🎉 no goals
    · intro i _
      -- ⊢ 0 ≤ (fun z => if z = y then b else a) i
      simp only
      -- ⊢ 0 ≤ if i = y then b else a
      split_ifs <;> assumption
      -- ⊢ 0 ≤ b
                    -- 🎉 no goals
                    -- 🎉 no goals
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos trivial, hab]
      -- 🎉 no goals
    · intro i hi
      -- ⊢ i ∈ s
      simp only [Finset.mem_singleton, Finset.mem_insert] at hi
      -- ⊢ i ∈ s
      cases hi <;> subst i <;> assumption
      -- ⊢ i ∈ s
                   -- ⊢ x ∈ s
                   -- ⊢ y ∈ s
                               -- 🎉 no goals
                               -- 🎉 no goals
#align convex_iff_sum_mem convex_iff_sum_mem

theorem Finset.centerMass_mem_convexHull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
    t.centerMass w z ∈ convexHull R s :=
  (convex_convexHull R s).centerMass_mem hw₀ hws fun i hi => subset_convexHull R s <| hz i hi
#align finset.center_mass_mem_convex_hull Finset.centerMass_mem_convexHull

/-- A refinement of `Finset.centerMass_mem_convexHull` when the indexed family is a `Finset` of
the space. -/
theorem Finset.centerMass_id_mem_convexHull (t : Finset E) {w : E → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i in t, w i) : t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.centerMass_mem_convexHull hw₀ hws fun _ => mem_coe.2
#align finset.center_mass_id_mem_convex_hull Finset.centerMass_id_mem_convexHull

theorem affineCombination_eq_centerMass {ι : Type*} {t : Finset ι} {p : ι → E} {w : ι → R}
    (hw₂ : ∑ i in t, w i = 1) : t.affineCombination R p w = centerMass t w p := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_zero, t.centerMass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]
  -- 🎉 no goals
#align affine_combination_eq_center_mass affineCombination_eq_centerMass

theorem affineCombination_mem_convexHull {s : Finset ι} {v : ι → E} {w : ι → R}
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1) :
    s.affineCombination R v w ∈ convexHull R (range v) := by
  rw [affineCombination_eq_centerMass hw₁]
  -- ⊢ centerMass s (fun i => w i) v ∈ ↑(convexHull R) (Set.range v)
  apply s.centerMass_mem_convexHull hw₀
  -- ⊢ 0 < ∑ i in s, w i
  · simp [hw₁]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
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
  -- ⊢ centerMass s (centroidWeights R s) id ∈ ↑(convexHull R) ↑s
  apply s.centerMass_id_mem_convexHull
  -- ⊢ ∀ (i : E), i ∈ s → 0 ≤ centroidWeights R s i
  · simp only [inv_nonneg, imp_true_iff, Nat.cast_nonneg, Finset.centroidWeights_apply]
    -- 🎉 no goals
  · have hs_card : (s.card : R) ≠ 0 := by simp [Finset.nonempty_iff_ne_empty.mp hs]
    -- ⊢ 0 < ∑ i in s, centroidWeights R s i
    simp only [hs_card, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel, Ne.def, not_false_iff,
      Finset.centroidWeights_apply, zero_lt_one]
#align finset.centroid_mem_convex_hull Finset.centroid_mem_convexHull

theorem convexHull_range_eq_exists_affineCombination (v : ι → E) : convexHull R (range v) =
    { x | ∃ (s : Finset ι) (w : ι → R) (_ : ∀ i ∈ s, 0 ≤ w i) (_ : s.sum w = 1),
    s.affineCombination R v w = x } := by
  refine' Subset.antisymm (convexHull_min _ _) _
  · intro x hx
    -- ⊢ x ∈ {x | ∃ s w x_1 x_2, ↑(affineCombination R s v) w = x}
    obtain ⟨i, hi⟩ := Set.mem_range.mp hx
    -- ⊢ x ∈ {x | ∃ s w x_1 x_2, ↑(affineCombination R s v) w = x}
    refine' ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
    -- 🎉 no goals
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    -- ⊢ a • ↑(affineCombination R s v) w + b • ↑(affineCombination R s' v) w' ∈ {x | …
    let W : ι → R := fun i => (if i ∈ s then a * w i else 0) + if i ∈ s' then b * w' i else 0
    -- ⊢ a • ↑(affineCombination R s v) w + b • ↑(affineCombination R s' v) w' ∈ {x | …
    have hW₁ : (s ∪ s').sum W = 1 := by
      rw [sum_add_distrib, ← sum_subset (subset_union_left s s'),
        ← sum_subset (subset_union_right s s'), sum_ite_of_true _ _ fun i hi => hi,
        sum_ite_of_true _ _ fun i hi => hi, ← mul_sum, ← mul_sum, hw₁, hw₁', ← add_mul, hab,
        mul_one] <;> intro i _ hi' <;> simp [hi']
    refine' ⟨s ∪ s', W, _, hW₁, _⟩
    -- ⊢ ∀ (i : ι), i ∈ s ∪ s' → 0 ≤ W i
    · rintro i -
      -- ⊢ 0 ≤ W i
      by_cases hi : i ∈ s <;> by_cases hi' : i ∈ s' <;>
      -- ⊢ 0 ≤ W i
                              -- ⊢ 0 ≤ W i
                              -- ⊢ 0 ≤ W i
        simp [hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
        -- 🎉 no goals
        -- 🎉 no goals
        -- 🎉 no goals
        -- 🎉 no goals
    · simp_rw [affineCombination_eq_linear_combination (s ∪ s') v _ hW₁,
        affineCombination_eq_linear_combination s v w hw₁,
        affineCombination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib]
      rw [← sum_subset (subset_union_left s s'), ← sum_subset (subset_union_right s s')]
      · simp only [ite_smul, sum_ite_of_true _ _ fun _ hi => hi, mul_smul, ← smul_sum]
        -- 🎉 no goals
      · intro i _ hi'
        -- ⊢ (if i ∈ s' then b * w' i else 0) • v i = 0
        simp [hi']
        -- 🎉 no goals
      · intro i _ hi'
        -- ⊢ (if i ∈ s then a * w i else 0) • v i = 0
        simp [hi']
        -- 🎉 no goals
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    -- ⊢ ↑(affineCombination R s v) w ∈ ↑(convexHull R) (Set.range v)
    exact affineCombination_mem_convexHull hw₀ hw₁
    -- 🎉 no goals
#align convex_hull_range_eq_exists_affine_combination convexHull_range_eq_exists_affineCombination

/--
Convex hull of `s` is equal to the set of all centers of masses of `Finset`s `t`, `z '' t ⊆ s`.
For universe reasons, you shouldn't use this lemma to prove that a given center of mass belongs
to the convex hull. Use convexity of the convex hull instead.
-/
theorem convexHull_eq (s : Set E) : convexHull R s =
    { x : E | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E) (_ : ∀ i ∈ t, 0 ≤ w i)
    (_ : ∑ i in t, w i = 1) (_ : ∀ i ∈ t, z i ∈ s), t.centerMass w z = x } := by
  refine' Subset.antisymm (convexHull_min _ _) _
  · intro x hx
    -- ⊢ x ∈ {x | ∃ ι t w z x_1 x_2 x_3, centerMass t w z = x}
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, Finset.sum_singleton,
      fun _ _ => hx
    simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
    -- 🎉 no goals
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha
      hb hab
    rw [Finset.centerMass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    -- ⊢ centerMass (disjSum sx sy) (Sum.elim (fun i => a * wx i) fun j => b * wy j)  …
    refine' ⟨_, _, _, _, _, _, _, rfl⟩
    · rintro i hi
      -- ⊢ 0 ≤ Sum.elim (fun i => a * wx i) (fun j => b * wy j) i
      rw [Finset.mem_disjSum] at hi
      -- ⊢ 0 ≤ Sum.elim (fun i => a * wx i) (fun j => b * wy j) i
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      -- ⊢ 0 ≤ Sum.elim (fun i => a * wx i) (fun j => b * wy j) (Sum.inl j)
                                                       -- ⊢ 0 ≤ a * wx j
                                                       -- ⊢ 0 ≤ b * wy j
        apply_rules [mul_nonneg, hwx₀, hwy₀]
        -- 🎉 no goals
        -- 🎉 no goals
    · simp [Finset.sum_sum_elim, Finset.mul_sum.symm, *]
      -- 🎉 no goals
    · intro i hi
      -- ⊢ Sum.elim zx zy i ∈ s
      rw [Finset.mem_disjSum] at hi
      -- ⊢ Sum.elim zx zy i ∈ s
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
      -- ⊢ Sum.elim zx zy (Sum.inl j) ∈ s
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    -- ⊢ centerMass t w z ∈ ↑(convexHull R) s
    exact t.centerMass_mem_convexHull hw₀ (hw₁.symm ▸ zero_lt_one) hz
    -- 🎉 no goals
#align convex_hull_eq convexHull_eq

theorem Finset.convexHull_eq (s : Finset E) : convexHull R ↑s =
    { x : E | ∃ (w : E → R) (_ : ∀ y ∈ s, 0 ≤ w y) (_ : ∑ y in s, w y = 1),
    s.centerMass w id = x } := by
  refine' Set.Subset.antisymm (convexHull_min _ _) _
  · intro x hx
    -- ⊢ x ∈ {x | ∃ w x_1 x_2, centerMass s w id = x}
    rw [Finset.mem_coe] at hx
    -- ⊢ x ∈ {x | ∃ w x_1 x_2, centerMass s w id = x}
    refine' ⟨_, _, _, Finset.centerMass_ite_eq _ _ _ hx⟩
    -- ⊢ ∀ (y : E), y ∈ s → 0 ≤ if x = y then 1 else 0
    · intros
      -- ⊢ 0 ≤ if x = y✝ then 1 else 0
      split_ifs
      -- ⊢ 0 ≤ 1
      exacts [zero_le_one, le_refl 0]
      -- 🎉 no goals
    · rw [Finset.sum_ite_eq, if_pos hx]
      -- 🎉 no goals
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    -- ⊢ a • centerMass s wx id + b • centerMass s wy id ∈ {x | ∃ w x_1 x_2, centerMa …
    rw [Finset.centerMass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    -- ⊢ centerMass s (fun i => a * wx i + b * wy i) id ∈ {x | ∃ w x_1 x_2, centerMas …
    refine' ⟨_, _, _, rfl⟩
    -- ⊢ ∀ (y : E), y ∈ s → 0 ≤ a * wx y + b * wy y
    · rintro i hi
      -- ⊢ 0 ≤ a * wx i + b * wy i
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
      -- 🎉 no goals
    · simp only [Finset.sum_add_distrib, Finset.mul_sum.symm, mul_one, *]
      -- 🎉 no goals
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    -- ⊢ centerMass s w id ∈ ↑(convexHull R) ↑s
    exact
      s.centerMass_mem_convexHull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx
#align finset.convex_hull_eq Finset.convexHull_eq

theorem Finset.mem_convexHull {s : Finset E} {x : E} : x ∈ convexHull R (s : Set E) ↔
    ∃ (w : E → R) (_ : ∀ y ∈ s, 0 ≤ w y) (_ : ∑ y in s, w y = 1), s.centerMass w id = x := by
  rw [Finset.convexHull_eq, Set.mem_setOf_eq]
  -- 🎉 no goals
#align finset.mem_convex_hull Finset.mem_convexHull

theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =
    { x : E | ∃ (w : E → R) (_ : ∀ y ∈ s, 0 ≤ w y) (_ : ∑ y in hs.toFinset, w y = 1),
    hs.toFinset.centerMass w id = x } := by
  simpa only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, exists_prop] using
    hs.toFinset.convexHull_eq
#align set.finite.convex_hull_eq Set.Finite.convexHull_eq

/-- A weak version of Carathéodory's theorem. -/
theorem convexHull_eq_union_convexHull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finset E) (w : ↑t ⊆ s), convexHull R ↑t := by
  refine' Subset.antisymm _ _
  -- ⊢ ↑(convexHull R) s ⊆ ⋃ (t : Finset E) (_ : ↑t ⊆ s), ↑(convexHull R) ↑t
  · rw [_root_.convexHull_eq]
    -- ⊢ {x | ∃ ι t w z x_1 x_2 x_3, centerMass t w z = x} ⊆ ⋃ (t : Finset E) (_ : ↑t …
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    -- ⊢ centerMass t w z ∈ ⋃ (t : Finset E) (_ : ↑t ⊆ s), ↑(convexHull R) ↑t
    simp only [mem_iUnion]
    -- ⊢ ∃ i i_1, centerMass t w z ∈ ↑(convexHull R) ↑i
    refine' ⟨t.image z, _, _⟩
    -- ⊢ ↑(Finset.image z t) ⊆ s
    · rw [coe_image, Set.image_subset_iff]
      -- ⊢ ↑t ⊆ z ⁻¹' s
      exact hz
      -- 🎉 no goals
    · apply t.centerMass_mem_convexHull hw₀
      -- ⊢ 0 < ∑ i in t, w i
      · simp only [hw₁, zero_lt_one]
        -- 🎉 no goals
      · exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
        -- 🎉 no goals
  · exact iUnion_subset fun i => iUnion_subset convexHull_mono
    -- 🎉 no goals
#align convex_hull_eq_union_convex_hull_finite_subsets convexHull_eq_union_convexHull_finite_subsets

theorem mk_mem_convexHull_prod {t : Set F} {x : E} {y : F} (hx : x ∈ convexHull R s)
    (hy : y ∈ convexHull R t) : (x, y) ∈ convexHull R (s ×ˢ t) := by
  rw [_root_.convexHull_eq] at hx hy ⊢
  -- ⊢ (x, y) ∈ {x | ∃ ι t_1 w z x_1 x_2 x_3, centerMass t_1 w z = x}
  obtain ⟨ι, a, w, S, hw, hw', hS, hSp⟩ := hx
  -- ⊢ (x, y) ∈ {x | ∃ ι t_1 w z x_1 x_2 x_3, centerMass t_1 w z = x}
  obtain ⟨κ, b, v, T, hv, hv', hT, hTp⟩ := hy
  -- ⊢ (x, y) ∈ {x | ∃ ι t_1 w z x_1 x_2 x_3, centerMass t_1 w z = x}
  have h_sum : ∑ i : ι × κ in a ×ˢ b, w i.fst * v i.snd = 1 := by
    rw [Finset.sum_product, ← hw']
    congr
    ext i
    have : ∑ y : κ in b, w i * v y = ∑ y : κ in b, v y * w i := by
      congr
      ext
      simp [mul_comm]
    rw [this, ← Finset.sum_mul, hv']
    simp
  refine'
    ⟨ι × κ, a ×ˢ b, fun p => w p.1 * v p.2, fun p => (S p.1, T p.2), fun p hp => _, h_sum,
      fun p hp => _, _⟩
  · rw [mem_product] at hp
    -- ⊢ 0 ≤ (fun p => w p.fst * v p.snd) p
    exact mul_nonneg (hw p.1 hp.1) (hv p.2 hp.2)
    -- 🎉 no goals
  · rw [mem_product] at hp
    -- ⊢ (fun p => (S p.fst, T p.snd)) p ∈ s ×ˢ t
    exact ⟨hS p.1 hp.1, hT p.2 hp.2⟩
    -- 🎉 no goals
  ext
  -- ⊢ (centerMass (a ×ˢ b) (fun p => w p.fst * v p.snd) fun p => (S p.fst, T p.snd …
  · rw [← hSp, Finset.centerMass_eq_of_sum_1 _ _ hw', Finset.centerMass_eq_of_sum_1 _ _ h_sum]
    -- ⊢ (∑ i in a ×ˢ b, (w i.fst * v i.snd) • (S i.fst, T i.snd)).fst = (∑ i in a, w …
    simp_rw [Prod.fst_sum, Prod.smul_mk]
    -- ⊢ ∑ x in a ×ˢ b, (w x.fst * v x.snd) • S x.fst = ∑ i in a, w i • S i
    rw [Finset.sum_product]
    -- ⊢ ∑ x in a, ∑ y in b, (w (x, y).fst * v (x, y).snd) • S (x, y).fst = ∑ i in a, …
    congr
    -- ⊢ (fun x => ∑ y in b, (w (x, y).fst * v (x, y).snd) • S (x, y).fst) = fun i => …
    ext i
    -- ⊢ ∑ y in b, (w (i, y).fst * v (i, y).snd) • S (i, y).fst = w i • S i
    have : (∑ j : κ in b, (w i * v j) • S i) = ∑ j : κ in b, v j • w i • S i := by
      congr
      ext
      rw [mul_smul, smul_comm]
    rw [this, ← Finset.sum_smul, hv', one_smul]
    -- 🎉 no goals
  · rw [← hTp, Finset.centerMass_eq_of_sum_1 _ _ hv', Finset.centerMass_eq_of_sum_1 _ _ h_sum]
    -- ⊢ (∑ i in a ×ˢ b, (w i.fst * v i.snd) • (S i.fst, T i.snd)).snd = (x, ∑ i in b …
    simp_rw [Prod.snd_sum, Prod.smul_mk]
    -- ⊢ ∑ x in a ×ˢ b, (w x.fst * v x.snd) • T x.snd = ∑ i in b, v i • T i
    rw [Finset.sum_product, Finset.sum_comm]
    -- ⊢ ∑ y in b, ∑ x in a, (w (x, y).fst * v (x, y).snd) • T (x, y).snd = ∑ i in b, …
    congr
    -- ⊢ (fun y => ∑ x in a, (w (x, y).fst * v (x, y).snd) • T (x, y).snd) = fun i => …
    ext j
    -- ⊢ ∑ x in a, (w (x, j).fst * v (x, j).snd) • T (x, j).snd = v j • T j
    simp_rw [mul_smul]
    -- ⊢ ∑ x in a, w x • v j • T j = v j • T j
    rw [← Finset.sum_smul, hw', one_smul]
    -- 🎉 no goals
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
  simp_rw [← image2_add, ← image_prod, IsLinearMap.isLinearMap_add.convexHull_image,
    convexHull_prod]
#align convex_hull_add convexHull_add

variable (R E)

-- porting note: needs `noncomputable` due to `OrderHom.toFun`!?
/-- `convexHull` is an additive monoid morphism under pointwise addition. -/
@[simps]
noncomputable def convexHullAddMonoidHom : Set E →+ Set E where
  toFun := convexHull R
  map_add' := convexHull_add
  map_zero' := convexHull_zero
#align convex_hull_add_monoid_hom convexHullAddMonoidHom

variable {R E}

theorem convexHull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convexHull_add, convexHull_neg]
  -- 🎉 no goals
#align convex_hull_sub convexHull_sub

theorem convexHull_list_sum (l : List (Set E)) : convexHull R l.sum = (l.map <| convexHull R).sum :=
  map_list_sum (convexHullAddMonoidHom R E) l
#align convex_hull_list_sum convexHull_list_sum

theorem convexHull_multiset_sum (s : Multiset (Set E)) :
    convexHull R s.sum = (s.map <| convexHull R).sum :=
  map_multiset_sum (convexHullAddMonoidHom R E) s
#align convex_hull_multiset_sum convexHull_multiset_sum

theorem convexHull_sum {ι} (s : Finset ι) (t : ι → Set E) :
    convexHull R (∑ i in s, t i) = ∑ i in s, convexHull R (t i) :=
  map_sum (convexHullAddMonoidHom R E) _ _
#align convex_hull_sum convexHull_sum

/-! ### `stdSimplex` -/


variable (ι) [Fintype ι] {f : ι → R}

/-- `stdSimplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
theorem convexHull_basis_eq_stdSimplex :
    convexHull R (range fun i j : ι => if i = j then (1 : R) else 0) = stdSimplex R ι := by
  refine' Subset.antisymm (convexHull_min _ (convex_stdSimplex R ι)) _
  -- ⊢ (Set.range fun i j => if i = j then 1 else 0) ⊆ stdSimplex R ι
  · rintro _ ⟨i, rfl⟩
    -- ⊢ (fun i j => if i = j then 1 else 0) i ∈ stdSimplex R ι
    exact ite_eq_mem_stdSimplex R i
    -- 🎉 no goals
  · rintro w ⟨hw₀, hw₁⟩
    -- ⊢ w ∈ ↑(convexHull R) (Set.range fun i j => if i = j then 1 else 0)
    rw [pi_eq_sum_univ w, ← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    -- ⊢ (centerMass Finset.univ (fun i => w i) fun i j => if i = j then 1 else 0) ∈  …
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i) (hw₁.symm ▸ zero_lt_one)
      fun i _ => mem_range_self i
#align convex_hull_basis_eq_std_simplex convexHull_basis_eq_stdSimplex

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@Finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
theorem Set.Finite.convexHull_eq_image {s : Set E} (hs : s.Finite) : convexHull R s =
    haveI := hs.fintype
    (⇑(∑ x : s, (@LinearMap.proj R s _ (fun _ => R) _ _ x).smulRight x.1)) '' stdSimplex R s := by
  -- Porting note: Original proof didn't need to specify `hs.fintype`
  rw [← @convexHull_basis_eq_stdSimplex _ _ _ hs.fintype, ← LinearMap.convexHull_image,
    ← Set.range_comp]
  simp_rw [Function.comp]
  -- ⊢ ↑(convexHull R) s = ↑(convexHull R) (range fun x => ↑(∑ x : ↑s, LinearMap.sm …
  apply congr_arg
  -- ⊢ s = range fun x => ↑(∑ x : ↑s, LinearMap.smulRight (LinearMap.proj x) ↑x) fu …
  convert Subtype.range_coe.symm
  -- ⊢ (↑(∑ x : ↑s, LinearMap.smulRight (LinearMap.proj x) ↑x) fun j => if x✝ = j t …
  -- Porting note: Original proof didn't need to specify `hs.fintype` and `(1 : R)`
  simp [LinearMap.sum_apply, ite_smul _ (1 : R), Finset.filter_eq,
    @Finset.mem_univ _ hs.fintype _]
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
  -- ⊢ {x | ∃ s w x_1 x_2, ↑(affineCombination R s ↑b) w = x} = {x | ∀ (i : ι), 0 ≤ …
  ext x
  -- ⊢ x ∈ {x | ∃ s w x_1 x_2, ↑(affineCombination R s ↑b) w = x} ↔ x ∈ {x | ∀ (i : …
  refine' ⟨_, fun hx => _⟩
  -- ⊢ x ∈ {x | ∃ s w x_1 x_2, ↑(affineCombination R s ↑b) w = x} → x ∈ {x | ∀ (i : …
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    -- ⊢ 0 ≤ ↑(coord b i) (↑(affineCombination R s ↑b) w)
    by_cases hi : i ∈ s
    -- ⊢ 0 ≤ ↑(coord b i) (↑(affineCombination R s ↑b) w)
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      -- ⊢ 0 ≤ w i
      exact hw₀ i hi
      -- 🎉 no goals
    · rw [b.coord_apply_combination_of_not_mem hi hw₁]
      -- 🎉 no goals
  · have hx' : x ∈ affineSpan R (range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination R E).mp hx'
    -- ⊢ ↑(affineCombination R s ↑b) w ∈ {x | ∃ s w x_1 x_2, ↑(affineCombination R s  …
    refine' ⟨s, w, _, hw₁, rfl⟩
    -- ⊢ ∀ (i : ι), i ∈ s → 0 ≤ w i
    intro i hi
    -- ⊢ 0 ≤ w i
    specialize hx i
    -- ⊢ 0 ≤ w i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    -- ⊢ 0 ≤ w i
    exact hx
    -- 🎉 no goals
#align affine_basis.convex_hull_eq_nonneg_coord AffineBasis.convexHull_eq_nonneg_coord

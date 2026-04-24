/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Shifting an affine subspace towards a point

This file introduces a "shift" transformation of affine subspace, where the subspace is translated
relatively to a point `c`. This is equivalent to `AffineSubspace.map (AffineEquiv.constVAdd ..)`,
but hides the detail of arbitrarily choosing a point in the subspace.

Shifting is controlled by a parameter `r`, indicating how far the output space is to `c`. We set
`r = 0` to mean the output space passes through `c` (See `AffineSubspace.shift_zero`),
while `r = 1` means not moving the input space at all (See `AffineSubspace.shift_one`).
With this convention, this transformation is also equivalent to `AffineSubspace.map (homothety c r)`
when `r` is a unit.

## Main declarations
* `AffineSubspace.shift` defines the shift transformation.
* `AffineSubspace.shift_eq` shows the shift transformation is equivalent to translation.
* `AffineSubspace.shift_eq_map_homothety` shows the shift transformation is equivalent to homothety.
-/

public section

open Module Submodule Finset AffineMap AffineSubspace

variable {k V P : Type*}

namespace AffineSubspace

section Ring
variable [Ring k] [AddCommGroup V] [AddTorsor V P] [Module k V]

open Classical in
/-- `AffineSubspace.shift s c r` is an affine subspace parallel to `s`, where an arbitrary point on
`s` is moved towards `c` with linear interpolation by `r`. When `r = 0`, that point is moved onto
`c`. When `r = 1`, that point stays at the original position. A different choice of the point will
not affect the output (See `AffineSubspace.shift_eq`).

We define `AffineSubspace.shift ⊥ c r = ⊥` (See `AffineSubspace.shift_bot`). -/
noncomputable
def shift (s : AffineSubspace k P) (c : P) (r : k) : AffineSubspace k P :=
  if h : Nonempty s then
    s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ h.some))).toAffineMap
  else
    ⊥

@[simp]
theorem direction_shift (s : AffineSubspace k P) (c : P) (r : k) :
    (s.shift c r).direction = s.direction := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [shift, h]
  have h : Nonempty s := by simpa using h
  simp [shift, h]

@[simp]
theorem shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥ := by
  simp [shift]

@[simp]
theorem shift_top (c : P) (r : k) : shift ⊤ c r = ⊤ := by
  simp [shift, AffineEquiv.surjective]

/-- `AffineSubspace.shift s c r` can be represented by moving a point in the subspace
towards `c`. -/
theorem shift_eq {s : AffineSubspace k P} (p : s) (c : P) (r : k) :
    s.shift c r = s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p))).toAffineMap := by
  have h : Nonempty s := ⟨p⟩
  simp only [shift, h, ↓reduceDIte]
  ext q
  simp only [mem_map, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
  constructor <;> intro ⟨x, hx, heq⟩ <;> rw [← heq]
  · refine ⟨(1 - r) • (p.val -ᵥ h.some.val) +ᵥ x, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction (smul_mem _ _ ?_) hx
      apply vsub_mem_direction p.prop h.some.prop
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]
  · refine ⟨(1 - r) • (h.some.val -ᵥ p.val) +ᵥ x, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction (smul_mem _ _ ?_) hx
      apply vsub_mem_direction h.some.prop p.prop
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]

@[simp]
theorem shift_zero (s : AffineSubspace k P) [h : Nonempty s] (c : P) :
    s.shift c 0 = mk' c s.direction := by
  refine ext_of_direction_eq (by simp) ⟨c, ?_⟩
  suffices ∃ x ∈ s, (c -ᵥ h.some) +ᵥ x = c by simpa [shift, h]
  exact ⟨h.some, by simp⟩

@[simp]
theorem shift_one (s : AffineSubspace k P) (c : P) : s.shift c 1 = s := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using h
  simp [shift, h]

theorem affineCombination_mem_shift {ι : Type*} [Fintype ι] [Nontrivial ι]
    (p : ι → P) (i : ι) {w : ι → k} (hw : ∑ i, w i = 1) :
    affineCombination k univ p w ∈ (affineSpan k <| p '' {i}ᶜ).shift (p i) (1 - w i) := by
  rcases subsingleton_or_nontrivial k with _ | _
  · suffices (affineSpan k <| p '' {i}ᶜ) = ⊤ by simp [this]
    have : Subsingleton P := (AddTorsor.subsingleton_iff V P).mp <| Module.subsingleton k V
    simp
  classical
  obtain ⟨j, hj⟩ : Set.Nonempty {i}ᶜ := by
    by_contra
    simp at this
  rw [shift_eq ⟨p j, mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices ∃ q ∈ affineSpan k (p '' {i}ᶜ), w i • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w by
    simpa
  refine ⟨-(w i • (p i -ᵥ p j)) +ᵥ affineCombination k univ p w, ?_, by simp⟩
  rw [← affineCombination_affineCombinationSingleWeights k _ p (mem_univ i),
    ← affineCombination_affineCombinationSingleWeights k _ p (mem_univ j),
    affineCombination_vsub, ← map_smul, ← map_neg, weightedVSub_vadd_affineCombination]
  refine affineCombination_mem_affineSpan_image ?_ (fun i' _ hi ↦ ?_) _
  · simp [sum_add_distrib, ← mul_sum, hw]
  have hi : i' = i := by simpa using hi
  have hj : j ≠ i := by simpa using hj
  simp [hi, hj.symm]

theorem _root_.AffineIndependent.affineCombination_mem_shift_iff
    {ι : Type*} [Fintype ι] [Nontrivial ι] {p : ι → P}
    (h : AffineIndependent k p) (i : ι) {w : ι → k} (hw : ∑ i, w i = 1) (c : k) :
    affineCombination k univ p w ∈ (affineSpan k <| p '' {i}ᶜ).shift (p i) c ↔
    w i = 1 - c := by
  refine ⟨?_, fun h ↦ by simpa [h] using affineCombination_mem_shift p i hw⟩
  classical
  obtain ⟨j, hj⟩ : Set.Nonempty {i}ᶜ := by
    by_contra
    simp at this
  rw [shift_eq ⟨p j, mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices ∀ q ∈ affineSpan k (p '' {i}ᶜ),
    (1 - c) • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w → w i = 1 - c by simpa
  intro q hqmem heq
  obtain ⟨t, w', ht, hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan_image hqmem
  have ht : (t : Set ι).indicator w' i = 0 := Set.indicator_of_notMem (by simpa using ht) w'
  have hj : j ≠ i := by simpa using hj
  rw [affineCombination_indicator_subset _ _ t.subset_univ,
    ← affineCombination_affineCombinationSingleWeights k _ p (mem_univ i),
    ← affineCombination_affineCombinationSingleWeights k _ p (mem_univ j),
    affineCombination_vsub, ← map_smul, weightedVSub_vadd_affineCombination,
    h.affineCombination_eq_iff_eq ?_ hw] at heq
  · simpa [hj.symm, ht] using (heq i (mem_univ i)).symm
  · simp [sum_add_distrib, sum_indicator_subset, ← mul_sum, hw']

end Ring

section CommRing
variable [CommRing k] [AddCommGroup V] [AddTorsor V P] [Module k V]

/-- For a unit parameter, shifting is the same as mapping by homothety. -/
theorem shift_eq_map_homothety (s : AffineSubspace k P) (c : P) {r : k} (hr : IsUnit r) :
    s.shift c r = s.map (homothety c r) := by
  obtain ⟨t, ht⟩ := hr.exists_right_inv
  rcases s.eq_bot_or_nonempty with h | h
  · simp [h]
  have h : Nonempty s := by simpa using h
  rw [s.shift_eq h.some]
  ext p
  suffices (∃ y ∈ s, (1 - r) • (c -ᵥ h.some) +ᵥ y = p) ↔ ∃ y ∈ s, r • (y -ᵥ c) +ᵥ c = p by
    simpa [homothety_def]
  constructor <;> intro ⟨x, hmem, heq⟩ <;> rw [← heq]
  · refine ⟨t • (x -ᵥ h.some.val) +ᵥ h.some.val, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction ?_ h.some.prop
      exact smul_mem _ _ <| vsub_mem_direction hmem h.some.prop
    · rw [vadd_vsub_assoc, smul_add, smul_smul, ht, sub_eq_add_neg, add_smul, one_smul, one_smul,
        neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
      simp_rw [add_comm _ (r • (h.some.val -ᵥ c)), ← vadd_vadd]
      congrm _ +ᵥ $(vsub_vadd_comm x h.some.val c)
  · refine ⟨r • (x -ᵥ h.some.val) +ᵥ h.some.val, ?_, ?_⟩
    · refine vadd_mem_of_mem_direction ?_ h.some.prop
      exact smul_mem _ _ <| vsub_mem_direction hmem h.some.prop
    · rw [sub_eq_add_neg, add_smul, one_smul, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev,
        ← vadd_vadd, vadd_vadd _ _ h.some.val, ← smul_add, add_comm, vsub_add_vsub_cancel,
        vadd_vadd, add_comm, ← vadd_vadd, vsub_vadd]

end CommRing

end AffineSubspace

namespace Affine.Simplex

section Ring
variable [Ring k] [PartialOrder k] [IsOrderedAddMonoid k] [AddCommGroup V] [AddTorsor V P]
  [Module k V] {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1)) {x : k}

theorem closedInterior_inter_shift_zero [ZeroLEOneClass k] :
    s.closedInterior ∩ (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) 0 =
    {s.points i} := by
  ext p
  by_cases hp : p ∈ affineSpan k (Set.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff, range_faceOpposite_points, SetLike.mem_coe,
      s.independent.affineCombination_mem_shift_iff i hw,
      affineCombination_mem_closedInterior_iff hw]
    suffices (∀ (i : Fin (n + 1)), 0 ≤ w i ∧ w i ≤ 1) ∧ w i = 1 ↔
        (affineCombination k univ s.points) w = s.points i by
      simpa
    rw [← affineCombination_affineCombinationSingleWeights k _ s.points (mem_univ i),
      s.independent.affineCombination_eq_iff_eq hw (by simp)]
    refine ⟨fun ⟨h, hi⟩ ↦ ?_, fun h ↦ ⟨fun j ↦ ?_, ?_⟩⟩
    · intro j _
      by_cases hj : j = i
      · simp [hj, hi]
      · suffices w j = 0 by simp [this, hj]
        rw [← Finset.univ.sum_erase_add _ (mem_univ i), hi, add_eq_right,
          Finset.sum_eq_zero_iff_of_nonneg <| fun j _ ↦ (h j).1] at hw
        exact hw j (by simpa using hj)
    · rw [h j (mem_univ j)]
      by_cases hj : j = i <;> simp [hj]
    · simp [h i (mem_univ i)]
  · apply iff_of_false
    · apply not_and_of_not_left
      contrapose hp
      exact Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    · contrapose hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_affineSpan _ (by simp)

theorem disjoint_closedInterior_shift (hx : x < 0 ∨ 1 < x) :
    Disjoint s.closedInterior <|
    (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) x := by
  refine Set.disjoint_left.mpr fun p hleft hright ↦ ?_
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
    Set.mem_of_mem_of_subset hleft s.closedInterior_subset_affineSpan
  rw [range_faceOpposite_points, SetLike.mem_coe,
    s.independent.affineCombination_mem_shift_iff i hw] at hright
  rw [affineCombination_mem_closedInterior_iff hw] at hleft
  grind

end Ring

section Field
variable [Field k] [LinearOrder k] [IsOrderedRing k] [AddCommGroup V] [AddTorsor V P]
  [Module k V] {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1)) {x : k}

theorem closedInterior_inter_shift (hx : x ∈ Set.Icc 0 1) :
    s.closedInterior ∩ (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) x =
    homothety (s.points i) x '' (s.faceOpposite i).closedInterior := by
  by_cases! hx0 : x = 0
  · simpa [hx0, (s.faceOpposite i).nonempty_closedInterior]
      using s.closedInterior_inter_shift_zero i
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 hx0.symm
  ext p
  by_cases hp : p ∈ affineSpan k (Set.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff, range_faceOpposite_points, SetLike.mem_coe,
      s.independent.affineCombination_mem_shift_iff i hw,
      affineCombination_mem_closedInterior_iff hw, Set.mem_image]
    simp_rw [AffineMap.homothety_eq_iff_of_mul_eq_one (mul_inv_cancel₀ hx0),
      univ.homothety_affineCombination _ _ (mem_univ i)]
    simp only [↓existsAndEq, and_true]
    rw [faceOpposite, affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ (by
      simp [AffineMap.lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hw])]
    trans (∀ j ∈ ({i}ᶜ : Finset _), x⁻¹ * w j ∈ Set.Icc 0 1) ∧
      ∀ j ∉ ({i}ᶜ : Finset _), x⁻¹ * (w j - 1) + 1 = 0
    · refine ⟨fun ⟨hj, hi⟩ ↦ ⟨fun j hji ↦ ⟨?_, ?_⟩, fun j hji ↦ ?_⟩, fun ⟨hj, hi⟩ ↦ ?_⟩
      · exact mul_nonneg (by simpa using hx.1) (hj j).1
      · rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at hi
        rw [inv_mul_le_one₀ hxpos, hi, le_sub_iff_add_le, ← hw]
        apply Finset.add_le_sum (fun i _ ↦ (hj i).1) (mem_univ j) (mem_univ i)
        simpa using hji
      · have hji : j = i := by simpa using hji
        simp [hji, hi, hx0]
      · specialize hi i (by simp)
        have hix : w i = 1 - x := by grind
        refine ⟨?_, hix⟩
        suffices ∀ (j : Fin (n + 1)), 0 ≤ w j by
          refine fun j ↦ ⟨this j, ?_⟩
          contrapose! hw
          apply ne_of_gt
          rw [← Finset.sum_erase_add _ _ (mem_univ j)]
          apply lt_add_of_nonneg_of_lt (sum_nonneg fun i _ ↦ this i) hw
        intro j
        by_cases hji : j = i
        · rw [hji, hix]
          simpa using hx.2
        · specialize hj j (by simpa using hji)
          apply nonneg_of_mul_nonneg_right hj.1
          simpa using hxpos
    · congrm (∀ j, (hj : _) → ?_) ∧ ∀ j, (hj : _) → ?_
      · have hj : j ≠ i := by simpa using hj
        simp [lineMap_apply, hj]
      · have hj : j = i := by simpa using hj
        simp [lineMap_apply, hj]
  · apply iff_of_false
    · apply not_and_of_not_left
      contrapose hp
      exact Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    · contrapose hp
      rw [Set.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      apply homothety_mem (mem_affineSpan _ (by simp))
      obtain hq := Set.mem_of_mem_of_subset hq (s.faceOpposite i).closedInterior_subset_affineSpan
      exact Set.mem_of_mem_of_subset hq (affineSpan_mono _ (by simp))

end Field
end Affine.Simplex

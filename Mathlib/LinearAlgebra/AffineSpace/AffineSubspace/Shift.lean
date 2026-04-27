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
* `Affine.Simplex.closedInterior_inter_shift` shows the intersection of the closed interior of a
  simplex and a shifted face is the homothety of the face.
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

We define `AffineSubspace.shift ⊥ c r = ⊥` (See `AffineSubspace.shift_empty`). -/
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
theorem shift_empty (c : P) (r : k) : shift ⊥ c r = ⊥ := by
  simp [shift]

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
variable [Field k] [LinearOrder k] [IsOrderedRing k] [AddCommGroup V] [AddTorsor V P] [Module k V]
  {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1)) {x : k}

/-- Draw a subspace parallel to `Affine.Simplex.faceOpposite`. The cross-section created by it and
the `Affine.Simplex.closedInterior` is the closed interior of the face transformed by homothety. -/
theorem closedInterior_inter_shift (hx : x ∈ Set.Icc 0 1) :
    s.closedInterior ∩ (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) x =
    homothety (s.points i) x '' (s.faceOpposite i).closedInterior := by
  classical
  by_cases! hx0 : x = 0
  · rw [hx0, shift_zero, closedInterior_inter_affineSubspaceMk'_affineSpan_faceOpposite]
    have : Set.Nonempty (s.faceOpposite i).closedInterior := nonempty_closedInterior _
    aesop
  have hx0' : 0 < x := lt_of_le_of_ne hx.1 hx0.symm
  obtain ⟨q, hq⟩ := Classical.arbitrary (affineSpan k (Set.range (s.faceOpposite i).points))
  rw [shift_eq_map_homothety _ _ (IsUnit.mk0 _ hx0)]
  ext p
  by_cases hp : p ∈ (affineSpan k (Set.range s.points))
  · have hhom (q : P) : homothety (s.points i) x q = p ↔ homothety (s.points i) x⁻¹ p = q :=
      homothety_eq_iff_of_mul_eq_one (by simp [hx0])
    suffices p ∈ s.closedInterior ∧ (homothety (s.points i) x⁻¹) p ∈
        (affineSpan k (Set.range (s.faceOpposite i).points)) ↔
        homothety (s.points i) x⁻¹ p ∈ (s.faceOpposite i).closedInterior by
      simpa [hhom]
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [homothety_affineCombination _ _ _ (by simp), affineCombination_mem_closedInterior_iff hw1]
    conv_rhs => rw [faceOpposite]
    have hw' : ∑ j, ((1 - x⁻¹) • affineCombinationSingleWeights k i + x⁻¹ • w) j = 1 := by
      simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
      simp [hw1]
    simp_rw [lineMap_apply_module]
    rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw']
    have h1 : (∀ j ∈ ({i} : Finset _)ᶜ,
        ((1 - x⁻¹) • affineCombinationSingleWeights k i + x⁻¹ • w) j ∈ Set.Icc 0 1)
        ↔ ∀ j ≠ i, x⁻¹ • w j ∈ Set.Icc 0 1 := by
      constructor <;> intro h j hj
      · specialize h j (by simpa using hj)
        rw [Pi.add_apply, Pi.smul_apply, affineCombinationSingleWeights_apply_of_ne _ hj] at h
        simpa using h
      · specialize h j (by simpa using hj)
        rw [Pi.add_apply, Pi.smul_apply,
          affineCombinationSingleWeights_apply_of_ne _ (by simpa using hj)]
        simpa using h
    have h2 : (∀ i_1 ∉ ({i} : Finset _)ᶜ,
        ((1 - x⁻¹) • affineCombinationSingleWeights k i + x⁻¹ • w) i_1 = 0)
        ↔ 1 - x⁻¹ + x⁻¹ * w i = 0 := by simp
    rw [h1, h2, affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hw' q,
      vadd_mem_iff_mem_direction _ hq, weightedVSubOfPoint_apply,
      ← sum_erase_add _ _ (show i ∈ univ by simp), Submodule.add_mem_iff_right _ (sum_mem
      fun j hj ↦ smul_mem _ _ <| vsub_mem_direction (by simpa using hj) hq)]
    simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [affineCombinationSingleWeights_apply_self, mul_one]
    constructor <;> intro ⟨h1, h2⟩
    · have hi : 1 - x⁻¹ + x⁻¹ * w i = 0 := by
        by_contra! h
        rw [smul_mem_iff _ h, vsub_right_mem_direction_iff_mem hq] at h2
        simp at h2
      have hi' : x = 1 - w i := by grind
      refine ⟨fun j hj ↦ ⟨mul_nonneg (by simpa using hx.1) (h1 j).1, ?_⟩, hi⟩
      rw [inv_mul_le_one₀ (by simpa using hx0'), hi', ← hw1, ← sum_erase_eq_sub (by simp),
        ← sub_nonneg, ← sum_erase_eq_sub (by simpa using hj)]
      exact sum_nonneg (fun k _ ↦ (h1 k).1)
    · have hi : w i = 1 - x := by grind
      refine ⟨fun k ↦ ?_, by simp [h2]⟩
      by_cases hk : k = i
      · rw [hk, hi]
        grind
      · have hnonneg : 0 ≤ w k := nonneg_of_mul_nonneg_right (h1 k hk).1 (by simpa using hx0')
        refine ⟨hnonneg, (le_mul_of_one_le_left hnonneg ?_).trans (h1 k hk).2⟩
        rw [one_le_inv₀ hx0']
        exact hx.2
  · apply iff_of_false
    · apply not_and_of_not_left
      contrapose! hp
      exact Set.mem_of_mem_of_subset hp closedInterior_subset_affineSpan
    · contrapose! hp
      rw [Set.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      apply homothety_mem (mem_affineSpan _ (by simp))
      obtain hq := Set.mem_of_mem_of_subset hq (s.faceOpposite i).closedInterior_subset_affineSpan
      exact Set.mem_of_mem_of_subset hq (affineSpan_mono _ (by simp))

/-- Draw a subspace parallel to `Affine.Simplex.faceOpposite`. It is disjoint from the closed
interior of the simplex if the shift parameter is outside $[0, 1]$. -/
theorem closedInterior_inter_shift_eq_empty (hx : x ∉ Set.Icc 0 1) :
    s.closedInterior ∩ (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) x =
    ∅ := by
  have hx0 : x ≠ 0 := by
    contrapose! hx
    simp [hx]
  by_contra! h
  obtain ⟨z, hzi, hzs⟩ := h
  rw [shift_eq_map_homothety _ _ (IsUnit.mk0 _ hx0)] at hzs
  obtain hz := Set.mem_of_mem_of_subset hzi s.closedInterior_subset_affineSpan
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hz
  rw [s.affineCombination_mem_closedInterior_iff hw1] at hzi
  have hxi : 1 - x⁻¹ + x⁻¹ * w i ≠ 0 := by
    contrapose! hx
    have : w i = 1 - x := by grind
    specialize hzi i
    rw [this] at hzi
    grind
  obtain hzs := mem_map_of_mem (homothety (s.points i) x⁻¹) hzs
  obtain p := Classical.arbitrary (affineSpan k (Set.range (s.faceOpposite i).points))
  rw [AffineSubspace.map_map, ← homothety_mul, inv_mul_cancel₀ hx0, homothety_one,
    AffineSubspace.map_id, homothety_affineCombination _ _ _ (by simp),
    ← vsub_right_mem_direction_iff_mem p.prop,
    ← sum_smul_vsub_const_eq_affineCombination_vsub _ _ _ _ ?_,
    ← sum_erase_add _ _ (show i ∈ Finset.univ by simp), Submodule.add_mem_iff_right _ ?_,
    lineMap_apply_module, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    affineCombinationSingleWeights_apply_self, smul_eq_mul, smul_eq_mul, mul_one,
    smul_mem_iff _ hxi, vsub_right_mem_direction_iff_mem p.prop] at hzs
  · exact s.points_notMem_affineSpan_faceOpposite i hzs
  · refine Submodule.sum_mem _ fun j hj ↦ ?_
    refine smul_mem _ _ <| vsub_mem_direction (mem_affineSpan _ ?_) p.prop
    suffices ∃ k, k ≠ i ∧ s.points k = s.points j by simpa
    exact ⟨j, by simpa using hj⟩
  · simp [lineMap_apply_module, sum_add_distrib, ← mul_sum, hw1]

end Affine.Simplex

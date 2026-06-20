/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

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
    s.map <| AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ h.some))
  else
    ⊥

@[simp]
theorem direction_shift (s : AffineSubspace k P) (c : P) (r : k) :
    (s.shift c r).direction = s.direction := by
  rcases s.eq_bot_or_nonempty with h | h
  · simp [shift, h]
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

@[simp]
theorem shift_top (c : P) (r : k) : shift ⊤ c r = ⊤ := by
  simp [shift, AffineEquiv.surjective]

@[simp]
theorem shift_bot (c : P) (r : k) : shift ⊥ c r = ⊥ := by
  simp [shift]

/-- `AffineSubspace.shift s c r` can be represented by moving a point in the subspace
towards `c`. -/
theorem shift_eq {s : AffineSubspace k P} (p : s) (c : P) (r : k) :
    s.shift c r = s.map (AffineEquiv.constVAdd k P ((1 - r) • (c -ᵥ p))) := by
  have h : Nonempty s := ⟨p⟩
  simp only [shift, h, ↓reduceDIte]
  ext q
  simp only [mem_map, AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply]
  constructor <;> intro ⟨x, hx, heq⟩ <;> rw [← heq]
  · refine ⟨(1 - r) • (p.val -ᵥ h.some.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direction (smul_mem _ _ (vsub_mem_direction p.prop h.some.prop)) hx
    · rw [vadd_vadd, ← smul_add, vsub_add_vsub_cancel]
  · refine ⟨(1 - r) • (h.some.val -ᵥ p.val) +ᵥ x, ?_, ?_⟩
    · exact vadd_mem_of_mem_direction (smul_mem _ _ (vsub_mem_direction h.some.prop p.prop)) hx
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
  have h : Nonempty s := by simpa using! h
  simp [shift, h]

/-- Consider a point `A` with barycentric coordinates associated to a collection of points `P`.
If the coordinate associated to one of the points `Pᵢ` is `r`, then the point `A` is on the span
of `P \ {Pᵢ}` shifted towards `Pᵢ` with parameter `1 - r`. -/
theorem affineCombination_mem_shift {ι : Type*} [Fintype ι] [Nontrivial ι]
    (p : ι → P) (i : ι) {w : ι → k} (hw : ∑ i, w i = 1) :
    affineCombination k univ p w ∈ (affineSpan k <| p '' {i}ᶜ).shift (p i) (1 - w i) := by
  cases subsingleton_or_nontrivial k
  · suffices (affineSpan k <| p '' {i}ᶜ) = ⊤ by simp [this]
    have : Subsingleton P := (AddTorsor.subsingleton_iff V P).mp <| Module.subsingleton k V
    simp
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j, mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices ∃ q ∈ affineSpan k (p '' {i}ᶜ), w i • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w by
    simpa
  refine ⟨-(w i • (p i -ᵥ p j)) +ᵥ affineCombination k univ p w, ?_, by simp⟩
  rw [← affineCombination_piSingle k _ p (mem_univ i),
    ← affineCombination_piSingle k _ p (mem_univ j), affineCombination_vsub, ← map_smul, ← map_neg,
    weightedVSub_vadd_affineCombination]
  refine affineCombination_mem_affineSpan_image ?_ (fun i' _ hi ↦ by aesop) _
  simp [sum_add_distrib, ← mul_sum, hw]

/-- The iff version of `affineCombination_mem_shift` for affine independent points. -/
theorem _root_.AffineIndependent.affineCombination_mem_shift_iff
    {ι : Type*} [Fintype ι] [Nontrivial ι] {p : ι → P}
    (h : AffineIndependent k p) (i : ι) {w : ι → k} (hw : ∑ i, w i = 1) (c : k) :
    affineCombination k univ p w ∈ (affineSpan k <| p '' {i}ᶜ).shift (p i) c ↔
    w i = 1 - c := by
  classical
  refine ⟨?_, fun h ↦ by simpa [h] using affineCombination_mem_shift p i hw⟩
  obtain ⟨j, hj⟩ := exists_ne i
  rw [shift_eq ⟨p j, mem_affineSpan k <| Set.mem_image_of_mem _ hj⟩]
  suffices ∀ q ∈ affineSpan k (p '' {i}ᶜ),
    (1 - c) • (p i -ᵥ p j) +ᵥ q = affineCombination k univ p w → w i = 1 - c by simpa
  intro q hqmem heq
  obtain ⟨t, w', ht, hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan_image hqmem
  have ht : (t : Set ι).indicator w' i = 0 := Set.indicator_of_notMem (by simpa using ht) w'
  rw [affineCombination_indicator_subset _ _ t.subset_univ,
    ← affineCombination_piSingle k _ p (mem_univ i),
    ← affineCombination_piSingle k _ p (mem_univ j), affineCombination_vsub, ← map_smul,
    weightedVSub_vadd_affineCombination, h.affineCombination_eq_iff_eq ?_ hw] at heq
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
  have h : Nonempty s := by simpa using! h
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
      simp_rw [add_comm _ (r • (h.some.val -ᵥ c)), ← vadd_vadd, vsub_vadd_comm x h.some.val c]
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
  [Module k V] {n : ℕ} [NeZero n] (s : Affine.Simplex k P n) (i : Fin (n + 1))

/-- The base of a simplex shifted with parameter 0 intersects the closed interior only at the
vertex. -/
theorem closedInterior_inter_shift_zero [ZeroLEOneClass k] :
    s.closedInterior ∩ (affineSpan k <| s.points '' {i}ᶜ).shift (s.points i) 0 =
    {s.points i} := by
  refine subset_antisymm (fun p ⟨hp, hshift⟩ ↦ ?_) (by simp [s.point_mem_closedInterior i])
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
    s.closedInterior_subset_affineSpan hp
  suffices w = Pi.single i 1 by simp [this]
  rw [affineCombination_mem_closedInterior_iff hw] at hp
  rw [SetLike.mem_coe, s.independent.affineCombination_mem_shift_iff i hw, sub_zero] at hshift
  ext j
  by_cases hj : j = i
  · aesop
  rw [← univ.sum_erase_add w (mem_univ i), hshift, add_eq_right,
    sum_eq_zero_iff_of_nonneg fun j _ ↦ (hp j).1] at hw
  simp [hw j (by simpa using hj), hj]

/-- The base of a simplex shifted with parameter outside $[0, 1]$ does not intersect the closed
interior. -/
theorem disjoint_closedInterior_shift {x : k} (hx : x < 0 ∨ 1 < x) :
    Disjoint s.closedInterior <|
    (affineSpan k (Set.range (s.faceOpposite i).points)).shift (s.points i) x := by
  refine Set.disjoint_left.mpr fun p hleft hright ↦ ?_
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype <|
    s.closedInterior_subset_affineSpan hleft
  rw [range_faceOpposite_points, SetLike.mem_coe,
    s.independent.affineCombination_mem_shift_iff i hw] at hright
  rw [affineCombination_mem_closedInterior_iff hw] at hleft
  grind

end Ring

section Field
variable [Field k] [LinearOrder k] [IsOrderedRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

private theorem closedInterior_inter_shift_aux {n : ℕ} (i : Fin n) {x : k} (hxpos : 0 < x)
    (hx1 : x ≤ 1) {w : Fin n → k} (hw : ∑ i, w i = 1) :
    (∀ j, w j ∈ Set.Icc 0 1) ∧ w i = 1 - x ↔
    (∀ j, j ≠ i → x⁻¹ * w j ∈ Set.Icc 0 1) ∧ x⁻¹ * (w i - 1) + 1 = 0 := by
  rw [show x⁻¹ * (w i - 1) + 1 = 0 ↔ w i = 1 - x by grind]
  refine and_congr_left fun hi ↦ ⟨fun hj j hji ↦ ⟨?_, ?_⟩, fun hj ↦ ?_⟩
  · exact mul_nonneg (by simpa using hxpos.le) (hj j).1
  · rw [eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq] at hi
    rw [inv_mul_le_one₀ hxpos, hi, le_sub_iff_add_le, ← hw]
    exact add_le_sum (fun i _ ↦ (hj i).1) (mem_univ j) (mem_univ i) hji
  · suffices ∀ j, 0 ≤ w j from
      fun j ↦ ⟨this j, hw ▸ Finset.single_le_sum (fun j _ ↦ this j) (mem_univ j)⟩
    intro j
    by_cases hji : j = i <;> aesop

/-- A parallel cross-section of a simplex is the image of the base under a homothety. -/
theorem closedInterior_inter_shift {n : ℕ} [NeZero n] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) {x : k} (hx : x ∈ Set.Icc 0 1) :
    s.closedInterior ∩ (affineSpan k (s.points '' {i}ᶜ)).shift (s.points i) x =
    homothety (s.points i) x '' (s.faceOpposite i).closedInterior := by
  rcases hx.1.eq_or_lt with hx0 | hxpos
  · simpa [hx0.symm, nonempty_closedInterior] using s.closedInterior_inter_shift_zero i
  ext p
  by_cases hp : p ∈ affineSpan k (.range s.points)
  · obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [Set.mem_inter_iff, SetLike.mem_coe, s.independent.affineCombination_mem_shift_iff i hw,
      affineCombination_mem_closedInterior_iff hw, Set.mem_image]
    simp_rw [AffineMap.homothety_eq_iff_of_mul_eq_one (mul_inv_cancel₀ hxpos.ne.symm),
      univ.homothety_affineCombination _ _ (mem_univ i)]
    simp only [↓existsAndEq, and_true]
    rw [faceOpposite, affineCombination_mem_closedInterior_face_iff_mem_Icc,
      closedInterior_inter_shift_aux i hxpos hx.2 hw]
    · simp only [mem_compl, mem_singleton, not_not, forall_eq]
      congrm (∀ j, (hj : _) → $(by simp [lineMap_apply, hj])) ∧ $(by simp [lineMap_apply])
    · simp [AffineMap.lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hw]
  · apply iff_of_false (hp <| s.closedInterior_subset_affineSpan ·.1)
    rintro ⟨q, hq, rfl⟩
    exact hp <| homothety_mem (mem_affineSpan _ (by simp)) _ <|
      affineSpan_mono _ (by simp) ((s.faceOpposite i).closedInterior_subset_affineSpan hq)

end Field
end Affine.Simplex

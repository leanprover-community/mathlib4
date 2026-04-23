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

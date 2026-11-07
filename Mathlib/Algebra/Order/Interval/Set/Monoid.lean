/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Interval.Set.Basic

import Mathlib.Data.Set.Function

/-!
# Images of intervals under `(+ d)`

The lemmas in this file state that addition maps intervals bijectively. The typeclass
`ExistsAddOfLE` is defined specifically to make them work when combined with
`IsOrderedCancelAddMonoid`; the lemmas below therefore apply to all ordered groups,
but also to `ℕ` and `ℝ≥0`, which are not groups.
-/

public section

variable {M : Type*} (a b c d : M)

namespace Set
section IsOrderedCancelAddMonoid
variable [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M] [ExistsAddOfLE M]

theorem Ici_add_bij : BijOn (· + d) (Ici a) (Ici (a + d)) := by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici, add_right_comm, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ioi_add_bij : BijOn (· + d) (Ioi a) (Ioi (a + d)) := by
  refine ⟨by simp [MapsTo], by simp, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi, add_right_comm, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Icc_add_bij : BijOn (· + d) (Icc a b) (Icc (a + d) (b + d)) := by
  rw [← Ici_inter_Iic, ← Ici_inter_Iic]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

theorem Ioo_add_bij : BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d)) := by
  rw [← Ioi_inter_Iio, ← Ioi_inter_Iio]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

theorem Ioc_add_bij : BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d)) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic]
  exact (Ioi_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => le_of_add_le_add_right hx.2

theorem Ico_add_bij : BijOn (· + d) (Ico a b) (Ico (a + d) (b + d)) := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iio]
  exact (Ici_add_bij a d).inter_mapsTo (by simp [MapsTo]) fun x hx => lt_of_add_lt_add_right hx.2

end IsOrderedCancelAddMonoid

/-!
### Images under `x ↦ a + x`
-/

section Left
variable [AddMonoid M] [PartialOrder M] [CanonicallyOrderedAdd M]

@[simp]
theorem image_const_add_Ici [AddLeftMono M] :
    (fun x => a + x) '' Ici b = Ici (a + b) := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact add_le_add_right hx a
  · obtain ⟨y, hy⟩ := exists_add_of_le hx
    refine ⟨_, self_le_add_right b y, ?_⟩
    rw [hy, add_assoc]

@[simp]
theorem image_const_add_Ioi [AddLeftStrictMono M] [IsLeftCancelAdd M] :
    (fun x => a + x) '' Ioi b = Ioi (a + b) := by
  ext x
  refine ⟨fun ⟨y, hy, hy'⟩ ↦ ?_, fun hx ↦ ?_⟩
  · exact hy' ▸ add_lt_add_right hy a
  · obtain ⟨y, hy⟩ := exists_add_of_le hx.le
    rw [add_assoc] at hy
    refine ⟨_, (self_le_add_right ..).lt_of_ne ?_, hy.symm⟩
    aesop

@[simp]
theorem image_const_add_Icc [AddLeftReflectLE M] :
    (fun x => a + x) '' Icc b c = Icc (a + b) (a + c) := by
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ ↦ ?_⟩
  · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    exact ⟨add_le_add_right hx₁ a, add_le_add_right hx₂ a⟩
  · obtain ⟨y, hy⟩ := exists_add_of_le hx₁
    rw [add_assoc] at hy
    exact ⟨_, ⟨self_le_add_right .., le_of_add_le_add_left (hy ▸ hx₂)⟩, hy.symm⟩

@[simp]
theorem image_const_add_Ico [AddLeftReflectLE M] [IsLeftCancelAdd M] :
    (fun x => a + x) '' Ico b c = Ico (a + b) (a + c) := by
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ ↦ ?_⟩
  · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨add_le_add_right hx₁ a, (add_le_add_right hx₂.le a).lt_of_ne ?_⟩
    aesop
  · obtain ⟨y, hy⟩ := exists_add_of_le hx₁
    rw [add_assoc] at hy
    refine ⟨_, ⟨self_le_add_right .., (le_of_add_le_add_left (hy ▸ hx₂.le)).lt_of_ne ?_⟩, hy.symm⟩
    aesop

@[simp]
theorem image_const_add_Ioc [AddLeftReflectLE M] [IsLeftCancelAdd M] :
    (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c) := by
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ ↦ ?_⟩
  · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨(add_le_add_right hx₁.le a).lt_of_ne ?_, add_le_add_right hx₂ a⟩
    aesop
  · obtain ⟨y, hy⟩ := exists_add_of_le hx₁.le
    rw [add_assoc] at hy
    refine ⟨_, ⟨(self_le_add_right ..).lt_of_ne ?_, le_of_add_le_add_left (hy ▸ hx₂)⟩, hy.symm⟩
    aesop

@[simp]
theorem image_const_add_Ioo [AddLeftReflectLE M] [IsLeftCancelAdd M] :
    (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c) := by
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ ↦ ?_⟩
  · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨(add_le_add_right hx₁.le a).lt_of_ne ?_, (add_le_add_right hx₂.le a).lt_of_ne ?_⟩ <;>
      aesop
  · obtain ⟨y, hy⟩ := exists_add_of_le hx₁.le
    rw [add_assoc] at hy
    refine ⟨_, ⟨(self_le_add_right ..).lt_of_ne ?_,
      (le_of_add_le_add_left (hy ▸ hx₂.le)).lt_of_ne ?_⟩, hy.symm⟩ <;> aesop

end Left

/-!
### Images under `x ↦ x + a`
-/

-- If we wanted to generalize these theorems to the noncommutative setting,
-- we'd need an opposite version of `ExistsAddOfLE`.
section Left
variable [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M] [ExistsAddOfLE M]

@[simp]
theorem image_add_const_Ici : (fun x => x + a) '' Ici b = Ici (b + a) :=
  (Ici_add_bij _ _).image_eq

@[simp]
theorem image_add_const_Ioi : (fun x => x + a) '' Ioi b = Ioi (b + a) :=
  (Ioi_add_bij _ _).image_eq

@[simp]
theorem image_add_const_Icc : (fun x => x + a) '' Icc b c = Icc (b + a) (c + a) :=
  (Icc_add_bij _ _ _).image_eq

@[simp]
theorem image_add_const_Ico : (fun x => x + a) '' Ico b c = Ico (b + a) (c + a) :=
  (Ico_add_bij _ _ _).image_eq

@[simp]
theorem image_add_const_Ioc : (fun x => x + a) '' Ioc b c = Ioc (b + a) (c + a) :=
  (Ioc_add_bij _ _ _).image_eq

@[simp]
theorem image_add_const_Ioo : (fun x => x + a) '' Ioo b c = Ioo (b + a) (c + a) :=
  (Ioo_add_bij _ _ _).image_eq

end Left
end Set

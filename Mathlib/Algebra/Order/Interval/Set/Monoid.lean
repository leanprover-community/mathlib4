/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Images of intervals under `(+ d)`

The lemmas in this file state that addition maps intervals bijectively. The typeclass
`ExistsAddOfLE` is defined specifically to make them work when combined with
`OrderedCancelAddCommMonoid`; the lemmas below therefore apply to all
`OrderedAddCommGroup`, but also to `ℕ` and `ℝ≥0`, which are not groups.
-/


namespace Set

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem Ici_add_bij : BijOn (· + d) (Ici a) (Ici (a + d)) := by
  refine
    ⟨fun x h => add_le_add_right (mem_Ici.mp h) _, (add_left_injective d).injOn, fun _ h => ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ici.mp h)
  rw [mem_Ici, add_right_comm, add_le_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Ioi_add_bij : BijOn (· + d) (Ioi a) (Ioi (a + d)) := by
  refine
    ⟨fun x h => add_lt_add_right (mem_Ioi.mp h) _, fun _ _ _ _ h => add_right_cancel h, fun _ h =>
      ?_⟩
  obtain ⟨c, rfl⟩ := exists_add_of_le (mem_Ioi.mp h).le
  rw [mem_Ioi, add_right_comm, add_lt_add_iff_right] at h
  exact ⟨a + c, h, by rw [add_right_comm]⟩

theorem Icc_add_bij : BijOn (· + d) (Icc a b) (Icc (a + d) (b + d)) := by
  rw [← Ici_inter_Iic, ← Ici_inter_Iic]
  exact
    (Ici_add_bij a d).inter_mapsTo (fun x hx => add_le_add_right hx _) fun x hx =>
      le_of_add_le_add_right hx.2

theorem Ioo_add_bij : BijOn (· + d) (Ioo a b) (Ioo (a + d) (b + d)) := by
  rw [← Ioi_inter_Iio, ← Ioi_inter_Iio]
  exact
    (Ioi_add_bij a d).inter_mapsTo (fun x hx => add_lt_add_right hx _) fun x hx =>
      lt_of_add_lt_add_right hx.2

theorem Ioc_add_bij : BijOn (· + d) (Ioc a b) (Ioc (a + d) (b + d)) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic]
  exact
    (Ioi_add_bij a d).inter_mapsTo (fun x hx => add_le_add_right hx _) fun x hx =>
      le_of_add_le_add_right hx.2

theorem Ico_add_bij : BijOn (· + d) (Ico a b) (Ico (a + d) (b + d)) := by
  rw [← Ici_inter_Iio, ← Ici_inter_Iio]
  exact
    (Ici_add_bij a d).inter_mapsTo (fun x hx => add_lt_add_right hx _) fun x hx =>
      lt_of_add_lt_add_right hx.2

/-!
### Images under `x ↦ x + a`
-/


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

/-!
### Images under `x ↦ a + x`
-/


@[simp]
theorem image_const_add_Ici : (fun x => a + x) '' Ici b = Ici (a + b) := by
  simp only [add_comm a, image_add_const_Ici]

@[simp]
theorem image_const_add_Ioi : (fun x => a + x) '' Ioi b = Ioi (a + b) := by
  simp only [add_comm a, image_add_const_Ioi]

@[simp]
theorem image_const_add_Icc : (fun x => a + x) '' Icc b c = Icc (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Icc]

@[simp]
theorem image_const_add_Ico : (fun x => a + x) '' Ico b c = Ico (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Ico]

@[simp]
theorem image_const_add_Ioc : (fun x => a + x) '' Ioc b c = Ioc (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Ioc]

@[simp]
theorem image_const_add_Ioo : (fun x => a + x) '' Ioo b c = Ioo (a + b) (a + c) := by
  simp only [add_comm a, image_add_const_Ioo]

end Set

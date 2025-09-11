/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Image
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.WithBot

/-!
# Intervals in `WithTop α` and `WithBot α`

In this file we prove various lemmas about `Set.image`s and `Set.preimage`s of intervals under
`some : α → WithTop α` and `some : α → WithBot α`.
-/

open Set

variable {α : Type*}

/-! ### `WithTop` -/

namespace WithTop

@[simp]
theorem preimage_coe_top : (some : α → WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun _ => coe_ne_top

variable [Preorder α] {a b : α}

theorem range_coe : range (some : α → WithTop α) = Iio ⊤ := by
  ext x
  rw [mem_Iio, WithTop.lt_top_iff_ne_top, mem_range, ne_top_iff_exists]

@[simp]
theorem preimage_coe_Ioi : (some : α → WithTop α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe

@[simp]
theorem preimage_coe_Ici : (some : α → WithTop α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe

@[simp]
theorem preimage_coe_Iio : (some : α → WithTop α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe

@[simp]
theorem preimage_coe_Iic : (some : α → WithTop α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe

@[simp]
theorem preimage_coe_Icc : (some : α → WithTop α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]

@[simp]
theorem preimage_coe_Ico : (some : α → WithTop α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]

@[simp]
theorem preimage_coe_Ioc : (some : α → WithTop α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_coe_Ioo : (some : α → WithTop α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]

@[simp]
theorem preimage_coe_Iio_top : (some : α → WithTop α) ⁻¹' Iio ⊤ = univ := by
  rw [← range_coe, preimage_range]

@[simp]
theorem preimage_coe_Ico_top : (some : α → WithTop α) ⁻¹' Ico a ⊤ = Ici a := by
  simp [← Ici_inter_Iio]

@[simp]
theorem preimage_coe_Ioo_top : (some : α → WithTop α) ⁻¹' Ioo a ⊤ = Ioi a := by
  simp [← Ioi_inter_Iio]

theorem image_coe_Ioi : (some : α → WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]

theorem image_coe_Ici : (some : α → WithTop α) '' Ici a = Ico (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]

theorem image_coe_Iio : (some : α → WithTop α) '' Iio a = Iio (a : WithTop α) := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

theorem image_coe_Iic : (some : α → WithTop α) '' Iic a = Iic (a : WithTop α) := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

theorem image_coe_Icc : (some : α → WithTop α) '' Icc a b = Icc (a : WithTop α) b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

theorem image_coe_Ico : (some : α → WithTop α) '' Ico a b = Ico (a : WithTop α) b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

theorem image_coe_Ioc : (some : α → WithTop α) '' Ioc a b = Ioc (a : WithTop α) b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

theorem image_coe_Ioo : (some : α → WithTop α) '' Ioo a b = Ioo (a : WithTop α) b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

theorem Ioi_coe : Ioi (a : WithTop α) = (↑) '' (Ioi a) ∪ {⊤} := by
  ext x; induction x <;> simp

theorem Ici_coe : Ici (a : WithTop α) = (↑) '' (Ici a) ∪ {⊤} := by
  ext x; induction x <;> simp

theorem Iio_coe : Iio (a : WithTop α) = (↑) '' (Iio a) := by
  ext x; induction x <;> simp

theorem Iic_coe : Iic (a : WithTop α) = (↑) '' (Iic a) := by
  ext x; induction x <;> simp

theorem Icc_coe : Icc (a : WithTop α) b = (↑) '' (Icc a b) := by
  ext x; induction x <;> simp

theorem Ico_coe : Ico (a : WithTop α) b = (↑) '' (Ico a b) := by
  ext x; induction x <;> simp

theorem Ioc_coe : Ioc (a : WithTop α) b = (↑) '' (Ioc a b) := by
  ext x; induction x <;> simp

theorem Ioo_coe : Ioo (a : WithTop α) b = (↑) '' (Ioo a b) := by
  ext x; induction x <;> simp

end WithTop

/-! ### `WithBot` -/

namespace WithBot

@[simp]
theorem preimage_coe_bot : (some : α → WithBot α) ⁻¹' {⊥} = (∅ : Set α) :=
  @WithTop.preimage_coe_top αᵒᵈ

variable [Preorder α] {a b : α}

theorem range_coe : range (some : α → WithBot α) = Ioi ⊥ :=
  @WithTop.range_coe αᵒᵈ _

@[simp]
theorem preimage_coe_Ioi : (some : α → WithBot α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe

@[simp]
theorem preimage_coe_Ici : (some : α → WithBot α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe

@[simp]
theorem preimage_coe_Iio : (some : α → WithBot α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe

@[simp]
theorem preimage_coe_Iic : (some : α → WithBot α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe

@[simp]
theorem preimage_coe_Icc : (some : α → WithBot α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]

@[simp]
theorem preimage_coe_Ico : (some : α → WithBot α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]

@[simp]
theorem preimage_coe_Ioc : (some : α → WithBot α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_coe_Ioo : (some : α → WithBot α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]

@[simp]
theorem preimage_coe_Ioi_bot : (some : α → WithBot α) ⁻¹' Ioi ⊥ = univ := by
  rw [← range_coe, preimage_range]

@[simp]
theorem preimage_coe_Ioc_bot : (some : α → WithBot α) ⁻¹' Ioc ⊥ a = Iic a := by
  simp [← Ioi_inter_Iic]

@[simp]
theorem preimage_coe_Ioo_bot : (some : α → WithBot α) ⁻¹' Ioo ⊥ a = Iio a := by
  simp [← Ioi_inter_Iio]

theorem image_coe_Iio : (some : α → WithBot α) '' Iio a = Ioo (⊥ : WithBot α) a := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iio]

theorem image_coe_Iic : (some : α → WithBot α) '' Iic a = Ioc (⊥ : WithBot α) a := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe, inter_comm, Ioi_inter_Iic]

theorem image_coe_Ioi : (some : α → WithBot α) '' Ioi a = Ioi (a : WithBot α) := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ioi_subset_Ioi bot_le)]

theorem image_coe_Ici : (some : α → WithBot α) '' Ici a = Ici (a : WithBot α) := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Ici_subset_Ioi.2 <| bot_lt_coe a)]

theorem image_coe_Icc : (some : α → WithBot α) '' Icc a b = Icc (a : WithBot α) b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]

theorem image_coe_Ioc : (some : α → WithBot α) '' Ioc a b = Ioc (a : WithBot α) b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioc_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]

theorem image_coe_Ico : (some : α → WithBot α) '' Ico a b = Ico (a : WithBot α) b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Ico_subset_Ici_self <| Ici_subset_Ioi.2 <| bot_lt_coe a)]

theorem image_coe_Ioo : (some : α → WithBot α) '' Ioo a b = Ioo (a : WithBot α) b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Ioi_self <| Ioi_subset_Ioi bot_le)]

theorem Ioi_coe : Ioi (a : WithBot α) = (↑) '' (Ioi a) := by
  ext x; induction x <;> simp

theorem Ici_coe : Ici (a : WithBot α) = (↑) '' (Ici a) := by
  ext x; induction x <;> simp

theorem Iio_coe : Iio (a : WithBot α) = (↑) '' (Iio a) ∪ {⊥} := by
  ext x; induction x <;> simp

theorem Iic_coe : Iic (a : WithBot α) = (↑) '' (Iic a) ∪ {⊥} := by
  ext x; induction x <;> simp

theorem Icc_coe : Icc (a : WithBot α) b = (↑) '' (Icc a b) := by
  ext x; induction x <;> simp

theorem Ico_coe : Ico (a : WithBot α) b = (↑) '' (Ico a b) := by
  ext x; induction x <;> simp

theorem Ioc_coe : Ioc (a : WithBot α) b = (↑) '' (Ioc a b) := by
  ext x; induction x <;> simp

theorem Ioo_coe : Ioo (a : WithBot α) b = (↑) '' (Ioo a b) := by
  ext x; induction x <;> simp

end WithBot

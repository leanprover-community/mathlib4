/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.WithBot

/-!
# Intervals in `WithTop α` and `WithBot α`

In this file we prove various lemmas about `Set.image`s and `Set.preimage`s of intervals under
`some : α → WithTop α` and `some : α → WithBot α`.
-/

public section

open Set

variable {α : Type*}

namespace WithTop

@[to_dual (attr := simp)]
theorem preimage_coe_top : (some : α → WithTop α) ⁻¹' {⊤} = (∅ : Set α) :=
  eq_empty_of_subset_empty fun _ => coe_ne_top

variable [Preorder α] {a b : α}

@[to_dual]
theorem range_coe : range (some : α → WithTop α) = Iio ⊤ := by
  ext; simp [mem_range, WithTop.lt_top_iff_ne_top, ne_top_iff_exists]

@[to_dual (attr := simp)]
theorem preimage_coe_Ioi : (some : α → WithTop α) ⁻¹' Ioi a = Ioi a :=
  ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]
theorem preimage_coe_Ici : (some : α → WithTop α) ⁻¹' Ici a = Ici a :=
  ext fun _ => coe_le_coe

@[to_dual (attr := simp)]
theorem preimage_coe_Iio : (some : α → WithTop α) ⁻¹' Iio a = Iio a :=
  ext fun _ => coe_lt_coe

@[to_dual (attr := simp)]
theorem preimage_coe_Iic : (some : α → WithTop α) ⁻¹' Iic a = Iic a :=
  ext fun _ => coe_le_coe

@[to_dual (attr := simp)]
theorem preimage_coe_Icc : (some : α → WithTop α) ⁻¹' Icc a b = Icc a b := by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]
theorem preimage_coe_Ico : (some : α → WithTop α) ⁻¹' Ico a b = Ico a b := by simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]
theorem preimage_coe_Ioc : (some : α → WithTop α) ⁻¹' Ioc a b = Ioc a b := by simp [← Ioi_inter_Iic]

@[to_dual (attr := simp)]
theorem preimage_coe_Ioo : (some : α → WithTop α) ⁻¹' Ioo a b = Ioo a b := by simp [← Ioi_inter_Iio]

@[to_dual (attr := simp)]
theorem preimage_coe_Iio_top : (some : α → WithTop α) ⁻¹' Iio ⊤ = univ := by
  rw [← range_coe, preimage_range]

@[to_dual (attr := simp)]
theorem preimage_coe_Ico_top : (some : α → WithTop α) ⁻¹' Ico a ⊤ = Ici a := by
  simp [← Ici_inter_Iio]

@[to_dual (attr := simp)]
theorem preimage_coe_Ioo_top : (some : α → WithTop α) ⁻¹' Ioo a ⊤ = Ioi a := by
  simp [← Ioi_inter_Iio]

@[to_dual]
theorem image_coe_Ioi : (some : α → WithTop α) '' Ioi a = Ioo (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ioi, image_preimage_eq_inter_range, range_coe, Ioi_inter_Iio]

@[to_dual]
theorem image_coe_Ici : (some : α → WithTop α) '' Ici a = Ico (a : WithTop α) ⊤ := by
  rw [← preimage_coe_Ici, image_preimage_eq_inter_range, range_coe, Ici_inter_Iio]

@[to_dual]
theorem image_coe_Iio : (some : α → WithTop α) '' Iio a = Iio (a : WithTop α) := by
  rw [← preimage_coe_Iio, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iio_subset_Iio le_top)]

@[to_dual]
theorem image_coe_Iic : (some : α → WithTop α) '' Iic a = Iic (a : WithTop α) := by
  rw [← preimage_coe_Iic, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Iic_subset_Iio.2 <| coe_lt_top a)]

@[to_dual]
theorem image_coe_Icc : (some : α → WithTop α) '' Icc a b = Icc (a : WithTop α) b := by
  rw [← preimage_coe_Icc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Icc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]
theorem image_coe_Ico : (some : α → WithTop α) '' Ico a b = Ico (a : WithTop α) b := by
  rw [← preimage_coe_Ico, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ico_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]
theorem image_coe_Ioc : (some : α → WithTop α) '' Ioc a b = Ioc (a : WithTop α) b := by
  rw [← preimage_coe_Ioc, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left
      (Subset.trans Ioc_subset_Iic_self <| Iic_subset_Iio.2 <| coe_lt_top b)]

@[to_dual]
theorem image_coe_Ioo : (some : α → WithTop α) '' Ioo a b = Ioo (a : WithTop α) b := by
  rw [← preimage_coe_Ioo, image_preimage_eq_inter_range, range_coe,
    inter_eq_self_of_subset_left (Subset.trans Ioo_subset_Iio_self <| Iio_subset_Iio le_top)]

@[to_dual]
theorem Ioi_coe : Ioi (a : WithTop α) = (↑) '' (Ioi a) ∪ {⊤} := by
  ext x; induction x <;> simp

@[to_dual]
theorem Ici_coe : Ici (a : WithTop α) = (↑) '' (Ici a) ∪ {⊤} := by
  ext x; induction x <;> simp

@[to_dual]
theorem Iio_coe : Iio (a : WithTop α) = (↑) '' (Iio a) := image_coe_Iio.symm

@[to_dual]
theorem Iic_coe : Iic (a : WithTop α) = (↑) '' (Iic a) := image_coe_Iic.symm

@[to_dual]
theorem Icc_coe : Icc (a : WithTop α) b = (↑) '' (Icc a b) := image_coe_Icc.symm

@[to_dual]
theorem Ico_coe : Ico (a : WithTop α) b = (↑) '' (Ico a b) := image_coe_Ico.symm

@[to_dual]
theorem Ioc_coe : Ioc (a : WithTop α) b = (↑) '' (Ioc a b) := image_coe_Ioc.symm

@[to_dual]
theorem Ioo_coe : Ioo (a : WithTop α) b = (↑) '' (Ioo a b) := image_coe_Ioo.symm

end WithTop

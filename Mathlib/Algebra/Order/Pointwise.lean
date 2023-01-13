/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.pointwise
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Bounds
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.

## TODO

`Sup (s • t) = Sup s • Sup t` and `Inf (s • t) = Inf s • Inf t` hold as well but
`covariant_class` is currently not polymorphic enough to state it.
-/


open Function Set

open Pointwise

variable {α : Type _}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

section One

variable [One α]

@[simp, to_additive]
theorem cSup_one : supₛ (1 : Set α) = 1 :=
  csupₛ_singleton _
#align cSup_one cSup_one

@[simp, to_additive]
theorem cInf_one : infₛ (1 : Set α) = 1 :=
  cinfₛ_singleton _
#align cInf_one cInf_one

end One

section Group

variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {s t : Set α}

@[to_additive]
theorem cSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : supₛ s⁻¹ = (infₛ s)⁻¹ :=
  by
  rw [← image_inv]
  exact ((OrderIso.inv α).map_cInf' hs₀ hs₁).symm
#align cSup_inv cSup_inv

@[to_additive]
theorem cInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : infₛ s⁻¹ = (supₛ s)⁻¹ :=
  by
  rw [← image_inv]
  exact ((OrderIso.inv α).map_cSup' hs₀ hs₁).symm
#align cInf_inv cInf_inv

@[to_additive]
theorem cSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    supₛ (s * t) = supₛ s * supₛ t :=
  csupₛ_image2_eq_csupₛ_csupₛ (fun _ => (OrderIso.mulRight _).to_galois_connection)
    (fun _ => (OrderIso.mulLeft _).to_galois_connection) hs₀ hs₁ ht₀ ht₁
#align cSup_mul cSup_mul

@[to_additive]
theorem cInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    infₛ (s * t) = infₛ s * infₛ t :=
  cinfₛ_image2_eq_cinfₛ_cinfₛ (fun _ => (OrderIso.mulRight _).symm.to_galois_connection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galois_connection) hs₀ hs₁ ht₀ ht₁
#align cInf_mul cInf_mul

@[to_additive]
theorem cSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    supₛ (s / t) = supₛ s / infₛ t := by
  rw [div_eq_mul_inv, cSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, cSup_inv ht₀ ht₁, div_eq_mul_inv]
#align cSup_div cSup_div

@[to_additive]
theorem cInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    infₛ (s / t) = infₛ s / supₛ t := by
  rw [div_eq_mul_inv, cInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, cInf_inv ht₀ ht₁, div_eq_mul_inv]
#align cInf_div cInf_div

end Group

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

section One

variable [One α]

@[simp, to_additive]
theorem Sup_one : supₛ (1 : Set α) = 1 :=
  supₛ_singleton
#align Sup_one Sup_one

@[simp, to_additive]
theorem Inf_one : infₛ (1 : Set α) = 1 :=
  infₛ_singleton
#align Inf_one Inf_one

end One

section Group

variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  (s t : Set α)

@[to_additive]
theorem Sup_inv (s : Set α) : supₛ s⁻¹ = (infₛ s)⁻¹ :=
  by
  rw [← image_inv, supₛ_image]
  exact ((OrderIso.inv α).map_Inf _).symm
#align Sup_inv Sup_inv

@[to_additive]
theorem Inf_inv (s : Set α) : infₛ s⁻¹ = (supₛ s)⁻¹ :=
  by
  rw [← image_inv, infₛ_image]
  exact ((OrderIso.inv α).map_Sup _).symm
#align Inf_inv Inf_inv

@[to_additive]
theorem Sup_mul : supₛ (s * t) = supₛ s * supₛ t :=
  (supₛ_image2_eq_supₛ_supₛ fun _ => (OrderIso.mulRight _).to_galois_connection) fun _ =>
    (OrderIso.mulLeft _).to_galois_connection
#align Sup_mul Sup_mul

@[to_additive]
theorem Inf_mul : infₛ (s * t) = infₛ s * infₛ t :=
  (infₛ_image2_eq_infₛ_infₛ fun _ => (OrderIso.mulRight _).symm.to_galois_connection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galois_connection
#align Inf_mul Inf_mul

@[to_additive]
theorem Sup_div : supₛ (s / t) = supₛ s / infₛ t := by simp_rw [div_eq_mul_inv, Sup_mul, Sup_inv]
#align Sup_div Sup_div

@[to_additive]
theorem Inf_div : infₛ (s / t) = infₛ s / supₛ t := by simp_rw [div_eq_mul_inv, Inf_mul, Inf_inv]
#align Inf_div Inf_div

end Group

end CompleteLattice

namespace LinearOrderedField

variable {K : Type _} [LinearOrderedField K] {a b r : K} (hr : 0 < r)

open Set

include hr

theorem smul_Ioo : r • Ioo a b = Ioo (r • a) (r • b) :=
  by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioo]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_lt_mul_left hr).mpr a_h_left_left
    exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(lt_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ioo LinearOrderedField.smul_Ioo

theorem smul_Icc : r • Icc a b = Icc (r • a) (r • b) :=
  by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Icc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_le_mul_left hr).mpr a_h_left_left
    exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(le_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Icc LinearOrderedField.smul_Icc

theorem smul_Ico : r • Ico a b = Ico (r • a) (r • b) :=
  by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ico]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_le_mul_left hr).mpr a_h_left_left
    exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(le_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ico LinearOrderedField.smul_Ico

theorem smul_Ioc : r • Ioc a b = Ioc (r • a) (r • b) :=
  by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    exact (mul_lt_mul_left hr).mpr a_h_left_left
    exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine' ⟨⟨(lt_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, _⟩
    rw [mul_div_cancel' _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ioc LinearOrderedField.smul_Ioc

theorem smul_Ioi : r • Ioi a = Ioi (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_lt_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (lt_div_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Ioi LinearOrderedField.smul_Ioi

theorem smul_Iio : r • Iio a = Iio (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Iio]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_lt_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (div_lt_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Iio LinearOrderedField.smul_Iio

theorem smul_Ici : r • Ici a = Ici (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_le_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (le_div_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Ici LinearOrderedField.smul_Ici

theorem smul_Iic : r • Iic a = Iic (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Iio]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_le_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    exact (div_le_iff' hr).mpr h
    exact mul_div_cancel' _ (ne_of_gt hr)
#align linear_ordered_field.smul_Iic LinearOrderedField.smul_Iic

end LinearOrderedField


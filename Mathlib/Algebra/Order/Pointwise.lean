/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Bounds
import Mathlib.Algebra.Order.Field.Basic -- Porting note: `LinearOrderedField`, etc
import Mathlib.Data.Set.Pointwise.SMul

#align_import algebra.order.pointwise from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.

## TODO

`sSup (s • t) = sSup s • sSup t` and `sInf (s • t) = sInf s • sInf t` hold as well but
`CovariantClass` is currently not polymorphic enough to state it.
-/


open Function Set

open Pointwise

variable {α : Type*}

-- Porting note: Swapped the place of `CompleteLattice` and `ConditionallyCompleteLattice`
-- due to simpNF problem between `sSup_xx` `csSup_xx`.

section CompleteLattice

variable [CompleteLattice α]

section One

variable [One α]

@[to_additive (attr := simp)]
theorem sSup_one : sSup (1 : Set α) = 1 :=
  sSup_singleton
#align Sup_zero sSup_zero
#align Sup_one sSup_one

@[to_additive (attr := simp)]
theorem sInf_one : sInf (1 : Set α) = 1 :=
  sInf_singleton
#align Inf_zero sInf_zero
#align Inf_one sInf_one

end One

section Group

variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  (s t : Set α)

@[to_additive]
theorem sSup_inv (s : Set α) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv, sSup_image]
  exact ((OrderIso.inv α).map_sInf _).symm
#align Sup_inv sSup_inv
#align Sup_neg sSup_neg

@[to_additive]
theorem sInf_inv (s : Set α) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv, sInf_image]
  exact ((OrderIso.inv α).map_sSup _).symm
#align Inf_inv sInf_inv
#align Inf_neg sInf_neg

@[to_additive]
theorem sSup_mul : sSup (s * t) = sSup s * sSup t :=
  (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection
#align Sup_mul sSup_mul
#align Sup_add sSup_add

@[to_additive]
theorem sInf_mul : sInf (s * t) = sInf s * sInf t :=
  (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection
#align Inf_mul sInf_mul
#align Inf_add sInf_add

@[to_additive]
theorem sSup_div : sSup (s / t) = sSup s / sInf t := by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]
#align Sup_div sSup_div
#align Sup_sub sSup_sub

@[to_additive]
theorem sInf_div : sInf (s / t) = sInf s / sSup t := by simp_rw [div_eq_mul_inv, sInf_mul, sInf_inv]
#align Inf_div sInf_div
#align Inf_sub sInf_sub

end Group

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

section One

variable [One α]

@[to_additive (attr := simp)]
theorem csSup_one : sSup (1 : Set α) = 1 :=
  csSup_singleton _
#align cSup_zero csSup_zero
#align cSup_one csSup_one

@[to_additive (attr := simp)]
theorem csInf_one : sInf (1 : Set α) = 1 :=
  csInf_singleton _
#align cInf_zero csInf_zero
#align cInf_one csInf_one

end One

section Group

variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {s t : Set α}

@[to_additive]
theorem csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv]
  exact ((OrderIso.inv α).map_csInf' hs₀ hs₁).symm
#align cSup_inv csSup_inv
#align cSup_neg csSup_neg

@[to_additive]
theorem csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv]
  exact ((OrderIso.inv α).map_csSup' hs₀ hs₁).symm
#align cInf_inv csInf_inv
#align cInf_neg csInf_neg

@[to_additive]
theorem csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sSup (s * t) = sSup s * sSup t :=
  csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁
#align cSup_mul csSup_mul
#align cSup_add csSup_add

@[to_additive]
theorem csInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sInf (s * t) = sInf s * sInf t :=
  csInf_image2_eq_csInf_csInf (fun _ => (OrderIso.mulRight _).symm.to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galoisConnection) hs₀ hs₁ ht₀ ht₁
#align cInf_mul csInf_mul
#align cInf_add csInf_add

@[to_additive]
theorem csSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sSup (s / t) = sSup s / sInf t := by
  rw [div_eq_mul_inv, csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, csSup_inv ht₀ ht₁, div_eq_mul_inv]
#align cSup_div csSup_div
#align cSup_sub csSup_sub

@[to_additive]
theorem csInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sInf (s / t) = sInf s / sSup t := by
  rw [div_eq_mul_inv, csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, csInf_inv ht₀ ht₁, div_eq_mul_inv]
#align cInf_div csInf_div
#align cInf_sub csInf_sub

end Group

end ConditionallyCompleteLattice

namespace LinearOrderedField

variable {K : Type*} [LinearOrderedField K] {a b r : K} (hr : 0 < r)

open Set

theorem smul_Ioo : r • Ioo a b = Ioo (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioo]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_lt_mul_left hr).mpr a_h_left_left
    · exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(lt_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ioo LinearOrderedField.smul_Ioo

theorem smul_Icc : r • Icc a b = Icc (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Icc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_le_mul_left hr).mpr a_h_left_left
    · exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(le_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Icc LinearOrderedField.smul_Icc

theorem smul_Ico : r • Ico a b = Ico (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ico]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_le_mul_left hr).mpr a_h_left_left
    · exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(le_div_iff' hr).mpr a_left, (div_lt_iff' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]
#align linear_ordered_field.smul_Ico LinearOrderedField.smul_Ico

theorem smul_Ioc : r • Ioc a b = Ioc (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_lt_mul_left hr).mpr a_h_left_left
    · exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(lt_div_iff' hr).mpr a_left, (div_le_iff' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]
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
    · exact (lt_div_iff' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)
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
    · exact (div_lt_iff' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)
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
    · exact (le_div_iff' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)
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
    · exact (div_le_iff' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)
#align linear_ordered_field.smul_Iic LinearOrderedField.smul_Iic

end LinearOrderedField

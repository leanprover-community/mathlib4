/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Sigma.Order
import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite intervals in a sigma type

This file provides the `LocallyFiniteOrder` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/


open Finset Function

namespace Sigma

variable {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

section LocallyFiniteOrder
variable [DecidableEq ι] [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrder (α i)]

instance instLocallyFiniteOrder : LocallyFiniteOrder (Σ i, α i) where
  finsetIcc := sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, lt_def, mem_Ico, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, lt_def, mem_Ioc, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, lt_def, mem_Ioo, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σ i, α i)

theorem card_Icc : #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Icc) _ _

theorem card_Ico : #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ico) _ _

theorem card_Ioc : #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioc) _ _

theorem card_Ioo : #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioo) _ _

end

variable (i : ι) (a b : α i)

@[simp]
theorem Icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
theorem Ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
theorem Ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
theorem Ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrderBot (α i)]

instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (Σ i, α i) where
  finsetIic | ⟨i, a⟩ => (Iic a).map (Embedding.sigmaMk i)
  finsetIio | ⟨i, a⟩ => (Iio a).map (Embedding.sigmaMk i)
  finset_mem_Iic := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def, hij.symm]
  finset_mem_Iio := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def, hij.symm]

variable (i : ι) (a : α i)

@[simp] theorem Iic_mk : Iic (⟨i, a⟩ : Sigma α) = (Iic a).map (Embedding.sigmaMk i) := rfl
@[simp] theorem Iio_mk : Iio (⟨i, a⟩ : Sigma α) = (Iio a).map (Embedding.sigmaMk i) := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrderTop (α i)]

instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (Σ i, α i) where
  finsetIci | ⟨i, a⟩ => (Ici a).map (Embedding.sigmaMk i)
  finsetIoi | ⟨i, a⟩ => (Ioi a).map (Embedding.sigmaMk i)
  finset_mem_Ici := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def]
  finset_mem_Ioi := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def]

variable (i : ι) (a : α i)

@[simp] theorem Ici_mk : Ici (⟨i, a⟩ : Sigma α) = (Ici a).map (Embedding.sigmaMk i) := rfl
@[simp] theorem Ioi_mk : Ioi (⟨i, a⟩ : Sigma α) = (Ioi a).map (Embedding.sigmaMk i) := rfl

end LocallyFiniteOrderTop

end Disjoint

end Sigma

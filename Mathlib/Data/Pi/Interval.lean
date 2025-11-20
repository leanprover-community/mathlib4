/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/

@[expose] public section


open Finset Fintype

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (α i)]

namespace Pi
section PartialOrder
variable [∀ i, PartialOrder (α i)]

section LocallyFiniteOrder
variable [∀ i, LocallyFiniteOrder (α i)]

instance instLocallyFiniteOrder : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_piFinset, mem_Icc, le_def, forall_and]

variable (a b : ∀ i, α i)

theorem Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) :=
  rfl

theorem card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i)) :=
  card_piFinset _

theorem card_Ico : #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioc : #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

theorem card_Ioo : #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [∀ i, LocallyFiniteOrderBot (α i)] (b : ∀ i, α i)

instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (∀ i, α i) :=
  .ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_piFinset, mem_Iic, le_def]

lemma card_Iic : #(Iic b) = ∏ i, #(Iic (b i)) := card_piFinset _
lemma card_Iio : #(Iio b) = ∏ i, #(Iic (b i)) - 1 := by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [∀ i, LocallyFiniteOrderTop (α i)] (a : ∀ i, α i)

instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_piFinset, mem_Ici, le_def]

lemma card_Ici : #(Ici a) = ∏ i, #(Ici (a i)) := card_piFinset _
lemma card_Ioi : #(Ioi a) = ∏ i, #(Ici (a i)) - 1 := by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

end LocallyFiniteOrderTop
end PartialOrder

section Lattice
variable [∀ i, Lattice (α i)] [∀ i, LocallyFiniteOrder (α i)] (a b : ∀ i, α i)

theorem uIcc_eq : uIcc a b = piFinset fun i => uIcc (a i) (b i) := rfl

theorem card_uIcc : #(uIcc a b) = ∏ i, #(uIcc (a i) (b i)) := card_Icc _ _

end Lattice
end Pi

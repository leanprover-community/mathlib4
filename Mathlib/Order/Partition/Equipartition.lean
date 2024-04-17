/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.Set.Equitable
import Mathlib.Order.Partition.Finpartition

#align_import order.partition.equipartition from "leanprover-community/mathlib"@"b363547b3113d350d053abdf2884e9850a56b205"

/-!
# Finite equipartitions

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `Finpartition.IsEquipartition`: Predicate for a `Finpartition` to be an equipartition.
-/


open Finset Fintype

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} (P : Finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def IsEquipartition : Prop :=
  (P.parts : Set (Finset α)).EquitableOn card
#align finpartition.is_equipartition Finpartition.IsEquipartition

theorem isEquipartition_iff_card_parts_eq_average :
    P.IsEquipartition ↔
      ∀ a : Finset α,
        a ∈ P.parts → a.card = s.card / P.parts.card ∨ a.card = s.card / P.parts.card + 1 :=
  by simp_rw [IsEquipartition, Finset.equitableOn_iff, P.sum_card_parts]
#align finpartition.is_equipartition_iff_card_parts_eq_average Finpartition.isEquipartition_iff_card_parts_eq_average

variable {P}

lemma not_isEquipartition :
    ¬P.IsEquipartition ↔ ∃ a ∈ P.parts, ∃ b ∈ P.parts, b.card + 1 < a.card :=
  Set.not_equitableOn

theorem Set.Subsingleton.isEquipartition (h : (P.parts : Set (Finset α)).Subsingleton) :
    P.IsEquipartition :=
  Set.Subsingleton.equitableOn h _
#align finpartition.set.subsingleton.is_equipartition Finpartition.Set.Subsingleton.isEquipartition

theorem IsEquipartition.card_parts_eq_average (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card ∨ t.card = s.card / P.parts.card + 1 :=
  P.isEquipartition_iff_card_parts_eq_average.1 hP _ ht
#align finpartition.is_equipartition.card_parts_eq_average Finpartition.IsEquipartition.card_parts_eq_average

theorem IsEquipartition.card_part_eq_average_iff (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card = s.card / P.parts.card ↔ t.card ≠ s.card / P.parts.card + 1 := by
  have a := hP.card_parts_eq_average ht
  have b : ¬(t.card = s.card / P.parts.card ∧ t.card = s.card / P.parts.card + 1) := by
    by_contra h; exact absurd (h.1 ▸ h.2) (lt_add_one _).ne
  tauto

theorem IsEquipartition.average_le_card_part (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    s.card / P.parts.card ≤ t.card := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le hP ht
#align finpartition.is_equipartition.average_le_card_part Finpartition.IsEquipartition.average_le_card_part

theorem IsEquipartition.card_part_le_average_add_one (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    t.card ≤ s.card / P.parts.card + 1 := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le_add_one hP ht
#align finpartition.is_equipartition.card_part_le_average_add_one Finpartition.IsEquipartition.card_part_le_average_add_one

theorem IsEquipartition.filter_neg_average_add_one_eq_average (hP : P.IsEquipartition) :
    P.parts.filter (fun p ↦ ¬p.card = s.card / P.parts.card + 1) =
    P.parts.filter (fun p ↦ p.card = s.card / P.parts.card) := by
  ext p
  simp only [mem_filter, and_congr_right_iff]
  exact fun hp ↦ (hP.card_part_eq_average_iff hp).symm

/-- An equipartition of a finset with `n` elements into `k` parts has
`n % k` parts of size `n / k + 1`. -/
theorem IsEquipartition.card_large_parts_eq_mod (hP : P.IsEquipartition) :
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card + 1).card = s.card % P.parts.card := by
  have z := P.sum_card_parts
  rw [← sum_filter_add_sum_filter_not (s := P.parts)
      (p := fun x ↦ x.card = s.card / P.parts.card + 1),
    hP.filter_neg_average_add_one_eq_average,
    sum_const_nat (m := s.card / P.parts.card + 1) (by simp),
    sum_const_nat (m := s.card / P.parts.card) (by simp),
    ← hP.filter_neg_average_add_one_eq_average,
    mul_add, add_comm, ← add_assoc, ← add_mul, mul_one, add_comm (Finset.card _),
    filter_card_add_filter_neg_card_eq_card, add_comm] at z
  rw [← add_left_inj, Nat.mod_add_div, z]

/-- An equipartition of a finset with `n` elements into `k` parts has
`n - n % k` parts of size `n / k`. -/
theorem IsEquipartition.card_small_parts_eq_mod (hP : P.IsEquipartition) :
    (P.parts.filter fun p ↦ p.card = s.card / P.parts.card).card =
    P.parts.card - s.card % P.parts.card := by
  conv_rhs =>
    arg 1
    rw [← filter_card_add_filter_neg_card_eq_card (p := fun p ↦ p.card = s.card / P.parts.card + 1)]
  rw [hP.card_large_parts_eq_mod, add_tsub_cancel_left, hP.filter_neg_average_add_one_eq_average]

/-! ### Discrete and indiscrete finpartition -/


variable (s) -- [Decidable (a = ⊥)]

theorem bot_isEquipartition : (⊥ : Finpartition s).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩
#align finpartition.bot_is_equipartition Finpartition.bot_isEquipartition

theorem top_isEquipartition [Decidable (s = ⊥)] : (⊤ : Finpartition s).IsEquipartition :=
  Set.Subsingleton.isEquipartition (parts_top_subsingleton _)
#align finpartition.top_is_equipartition Finpartition.top_isEquipartition

theorem indiscrete_isEquipartition {hs : s ≠ ∅} : (indiscrete hs).IsEquipartition := by
  rw [IsEquipartition, indiscrete_parts, coe_singleton]
  exact Set.equitableOn_singleton s _
#align finpartition.indiscrete_is_equipartition Finpartition.indiscrete_isEquipartition

end Finpartition

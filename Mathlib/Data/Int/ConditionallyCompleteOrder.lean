/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.int.conditionally_complete_order
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Data.Int.LeastGreatest

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/


open Int

open Classical

noncomputable section

instance : ConditionallyCompleteLinearOrder ℤ :=
  { Int.linearOrder,
    LinearOrder.toLattice with
    sup := fun s =>
      if h : s.Nonempty ∧ BddAbove s then
        greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    inf := fun s =>
      if h : s.Nonempty ∧ BddBelow s then
        leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    le_cSup := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (greatest_of_bdd _ _ _).2.2 n hns
    cSup_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (greatest_of_bdd _ (Classical.choose_spec this.2) _).2.1
    cInf_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (least_of_bdd _ _ _).2.2 n hns
    le_cInf := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (least_of_bdd _ (Classical.choose_spec this.2) _).2.1 }

namespace Int

theorem cSup_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : supₛ s = greatestOfBdd b Hb Hinh :=
  by
  convert dif_pos _ using 1
  · convert coe_greatest_of_bdd_eq _ (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) _
  · exact ⟨Hinh, b, Hb⟩
#align int.cSup_eq_greatest_of_bdd Int.cSup_eq_greatest_of_bdd

@[simp]
theorem cSup_empty : supₛ (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cSup_empty Int.cSup_empty

theorem cSup_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : supₛ s = 0 :=
  dif_neg (by simp [h])
#align int.cSup_of_not_bdd_above Int.cSup_of_not_bdd_above

theorem cInf_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : infₛ s = leastOfBdd b Hb Hinh :=
  by
  convert dif_pos _ using 1
  · convert coe_least_of_bdd_eq _ (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) _
  · exact ⟨Hinh, b, Hb⟩
#align int.cInf_eq_least_of_bdd Int.cInf_eq_least_of_bdd

@[simp]
theorem cInf_empty : infₛ (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cInf_empty Int.cInf_empty

theorem cInf_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : infₛ s = 0 :=
  dif_neg (by simp [h])
#align int.cInf_of_not_bdd_below Int.cInf_of_not_bdd_below

theorem cSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : supₛ s ∈ s :=
  by
  convert (greatest_of_bdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cSup_mem Int.cSup_mem

theorem cInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : infₛ s ∈ s :=
  by
  convert (least_of_bdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cInf_mem Int.cInf_mem

end Int


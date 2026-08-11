/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Conditions for `Fin.insertNth` to be monotone or strictly monotone

-/

public section

namespace Fin

variable {n : ℕ} {α : Type*} [Preorder α]

lemma insertNth_zero_monotone
    {f : Fin (n + 1) → α} (hf : Monotone f) (x : α) (hx : x ≤ f 0) :
    Monotone (Fin.insertNth 0 (α := fun _ ↦ α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i.castSucc_le_succ

lemma strictMono_insertNth_zero
    {f : Fin (n + 1) → α} (hf : StrictMono f) (x : α) (hx : x < f 0) :
    StrictMono (Fin.insertNth 0 (α := fun _ ↦ α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa
  · simpa using hf i

lemma insertNth_monotone
    {f : Fin (n + 1) → α} (hf : Monotone f) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc ≤ x) (hx₂ : x ≤ f i.succ) :
    Monotone (Fin.insertNth i.castSucc.succ (α := fun _ ↦ α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc, hf j.castSucc_le_succ]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above, hf j.castSucc_le_succ]

lemma strictMono_insertNth
    {f : Fin (n + 1) → α} (hf : StrictMono f) (i : Fin n) (x : α)
    (hx₁ : f i.castSucc < x) (hx₂ : x < f i.succ) :
    StrictMono (Fin.insertNth i.castSucc.succ (α := fun _ ↦ α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro j
  obtain hj | rfl | hj := lt_trichotomy j i.castSucc
  · obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    grind [insertNth_apply_below, castPred_castSucc]
  · rwa [← succAbove_succ_self i.castSucc, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
    grind [insertNth_apply_same, insertNth_apply_above]

lemma insertNth_last_monotone
    {f : Fin (n + 1) → α} (hf : Monotone f) (x : α) (hx : f (Fin.last n) ≤ x) :
    Monotone (Fin.insertNth (Fin.last (n + 1)) (α := fun _ ↦ α) x f) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i.castSucc_le_succ
  · simpa

lemma strictMono_insertNth_last
    {f : Fin (n + 1) → α} (hf : StrictMono f) (x : α) (hx : f (Fin.last n) < x) :
    StrictMono (Fin.insertNth (Fin.last (n + 1)) (α := fun _ ↦ α) x f) := by
  rw [Fin.strictMono_iff_lt_succ] at hf ⊢
  intro i
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simpa only [insertNth_last', snoc_castSucc, Fin.succ_castSucc]
      using hf i
  · simpa

end Fin

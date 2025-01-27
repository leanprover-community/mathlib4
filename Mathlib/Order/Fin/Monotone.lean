/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.Fin.Basic

/-!
# Monotone maps from `Fin`

In this file, we show that a map `f : Fin (n + 1) → α` is monotone
iff `f i.castSucc ≤ f i.succ` for all `i : Fin n`.

-/

universe u

namespace Fin

lemma monotone_iff {α : Type u} [Preorder α] {n : ℕ} (f : Fin (n + 1) → α) :
    Monotone f ↔ ∀ (i : Fin n), f i.castSucc ≤ f i.succ := by
  refine ⟨fun hf i ↦ hf i.castSucc_le_succ, fun hf ↦ ?_⟩
  let P (k : ℕ) := ∀ (i : ℕ) (hi : i + k ≤ n), f ⟨i, by omega⟩ ≤ f ⟨i + k, by omega⟩
  suffices ∀ k, P k by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : i ≤ j)
    obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact this k i (by omega)
  intro k
  induction k with
  | zero => simp [P]
  | succ k hk =>
      intro i hi
      simp only [← Nat.add_assoc]
      exact (hk i (by omega)).trans (hf ⟨i + k, by omega⟩)

lemma orderHom_injective_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) →o α) :
    Function.Injective f ↔ ∀ (i : Fin n), f i.castSucc ≠ f i.succ := by
  constructor
  · intro hf i h
    simpa [Fin.ext_iff] using hf h
  · intro hf i j h
    wlog hij : i ≤ j generalizing i j h
    · exact (this h.symm (by omega)).symm
    obtain ⟨k, hk⟩ := Nat.le.dest hij
    cases k with
    | zero => ext; omega
    | succ k =>
        let l : Fin n := ⟨i.1, by omega⟩
        have h₁ : f i < f l.succ := by
          rw [lt_iff_le_and_ne]
          exact ⟨f.monotone l.castSucc_le_succ, hf l⟩
        have h₂ : f i < f j := lt_of_lt_of_le h₁ (f.monotone (by
          simp only [Fin.le_def, val_succ, l]
          omega))
        exact (h₂.ne h).elim

lemma strictMono_iff {α : Type*} [PartialOrder α] {n : ℕ} (f : Fin (n + 1) → α) :
    StrictMono f ↔ ∀ (i : Fin n), f i.castSucc < f i.succ := by
  constructor
  · intro hf i
    exact hf (castSucc_lt_succ i)
  · intro h
    let φ : Fin (n + 1) →o α :=
      { toFun := f
        monotone' := by
          rw [monotone_iff]
          intro i
          exact (h i).le }
    refine (Monotone.strictMono_iff_injective (f := f) φ.monotone).2
      ((orderHom_injective_iff φ).2 (fun i hi ↦ ?_))
    dsimp [φ] at hi
    replace h := h i
    simp [hi] at h

end Fin

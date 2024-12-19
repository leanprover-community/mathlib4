import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card

/-!
This file defines various operations on permutations, necessary for working with `SymmOperad`s.
They seem unlikely to be of much use elsewhere, hence why they are all under the Operad folder.

Definitions:
  - PermFinPadLeftRight
  - PermFinPadTo
  - PermFinPadAt
-/
open Equiv

/-- Extend a permutation on Fin n to a permutation on Fim (m+n+k), by acting as the identity
 on the first m and last k elements. -/
def PermFinPadLeftRight {n : ℕ} (p : Perm (Fin n)) (m k : ℕ) : (Perm (Fin (m + n + k))) :=
  Perm.extendDomain p (p := fun x ↦ m ≤ x ∧ x < m + n) ⟨
    fun x ↦ ⟨(Fin.natAdd m x).castAdd k, by simp [Fin.natAdd, Fin.addNat]⟩,
    fun x ↦ ⟨(Fin.castLT x.1 (show x < n + m by omega)).subNat m (by simp [x.2.1]),
      Nat.sub_lt_left_of_lt_add x.2.1 x.2.2⟩,
    fun x ↦ by simp,
    fun x ↦ by
      ext
      simp only [Fin.coe_subNat, Fin.coe_castLT, Fin.natAdd_mk, Fin.castAdd_mk]
      omega
    ⟩

/-- PermfindPadTo is morally equivalent to PermfinPadLeftRight, but with a different type. It
  starts the permutation Sm at location k out of n, and creates a perm of length (n+m-1). -/
def PermFinPadTo {m : ℕ} (p : Perm (Fin m)) (n : ℕ) (k : Fin n) : Perm (Fin (n+m-1)) :=
  have h : (k + m + (n - (k + 1))) = n + m - 1 := by
    omega
  h ▸ PermFinPadLeftRight p k (n-(k+1))

def PermFinPadAt_core {m n : ℕ} (p : Perm (Fin m)) (hn : 0 < n) (k : Fin m) (x : Fin (m+n-1)) :
    Fin (m+n-1) :=
  if h : k.1 ≤ x.1 ∧ x.1 ≤ k + n - 1 then
    ⟨p k + x - k.1, by omega⟩
  else (
    let x' := if h₂ : x < k.1 then p ⟨x.1, h₂.trans k.2⟩ else p ⟨x.1 - (n-1), by omega⟩;
    if h₃ : x' < p k then ⟨x', by omega⟩ else ⟨x'+n-1, by omega⟩
  )

theorem PermFinPadAt_core.LeftInverse {m n : ℕ} (p : Perm (Fin m)) (hn : 0 < n) (k : Fin m) :
    Function.LeftInverse (PermFinPadAt_core p.symm hn (p k)) (PermFinPadAt_core p hn k) := by
  intro x
  rw [PermFinPadAt_core]
  split
  · suffices (k:ℕ) ≤ ↑x ∧ (x:ℕ) ≤ ↑k + n - 1 by
      suffices h : (PermFinPadAt_core p hn k x : ℕ) = (p k) + x - k ∧ (k:ℕ) ≤ x by
        ext
        simp only [symm_apply_apply]
        omega
      simp [PermFinPadAt_core, this]
    rename_i h₁
    rcases h₁ with ⟨h₁,h₂⟩
    by_contra h₃
    rw [PermFinPadAt_core, dif_neg h₃] at h₁ h₂
    rw [Decidable.not_and_iff_or_not_not] at h₃
    push_neg at h₃
    have h₄ : p ⟨x - (n-1), proof_3 hn k x⟩ ≠ p k := by
      simpa using Fin.ne_of_val_ne (show x - (n-1) ≠ k by omega)
    rcases h₃ with h₃|h₃
    · simp only [dif_pos h₃] at h₁ h₂
      split at h₁
      <;> rename_i h₄
      <;> simp only [h₄, ↓reduceDIte] at h₂
      · dsimp at h₁
        omega
      · refine (?_:¬_) (show (p ⟨↑x, proof_2 k x (of_eq_true (eq_true h₃))⟩) = p k by omega)
        simpa [Fin.ext_iff] using Nat.ne_of_lt h₃
    · simp [show ¬(x:ℕ) < k by omega] at h₁ h₂
      split at h₁
      <;> rename_i h₄
      <;> simp only [h₄, ↓reduceDIte] at h₂
      <;> simp only [Fin.val_fin_le] at h₁
      <;> omega
  · rename_i h₁
    rw [Decidable.not_and_iff_or_not_not] at h₁
    push_neg at h₁
    rcases h₁ with h₁|h₁
    · simp only [dif_pos h₁, symm_apply_apply]
      by_cases h₂ : (k:ℕ) ≤ x
      · simp [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂]
        have h₃ : ¬(x:ℕ) ≤ ↑k + n - 1 := by
          by_contra! h₃
          simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, true_and, ↓reduceDIte] at h₁
          omega
        simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, and_false, ↓reduceDIte] at h₁
        simp only [h₃, ↓reduceDIte, and_false]
        split at h₁
        · rename_i h₄
          simp only [h₄, ↓reduceDIte, Fin.eta, symm_apply_apply]
          split
          · exfalso
            rename_i h₅
            simp only [Fin.lt_def] at h₅
            omega
          · ext
            dsimp
            omega
        · absurd h₁
          dsimp
          omega
      · simp [PermFinPadAt_core, h₂, Nat.gt_of_not_le h₂]
        split
        · simpa using fun h ↦ (h₂ h).elim
        · rename_i h₃
          simp only [PermFinPadAt_core, h₂, Nat.gt_of_not_le h₂, h₃, false_and, ↓reduceDIte] at h₁
          omega
    · simp only [dif_neg (show ¬(PermFinPadAt_core p hn k x : ℕ) < p k by omega), symm_apply_apply]
      by_cases h₂ : (k:ℕ) ≤ x
      · simp only [PermFinPadAt_core, h₂, true_and, dif_neg (Nat.not_lt.mpr h₂)]
        have h₃ : ¬(x:ℕ) ≤ ↑k + n - 1 := by
          by_contra! h₃
          simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, true_and, ↓reduceDIte] at h₁
          omega
        simp only [PermFinPadAt_core, h₂, Nat.not_lt.mpr h₂, h₃, and_false, ↓reduceDIte] at h₁
        simp only [dif_neg h₃]
        split at h₁
        · absurd h₁
          dsimp
          omega
        · rename_i h₄
          simp only [dif_neg h₄]
          generalize_proofs pf1 pf2
          have h₆ : (⟨↑(p ⟨↑x - (n - 1), pf1⟩) + n - 1 - (n - 1), pf2⟩ : Fin m) =
              p ⟨↑x - (n - 1), pf1⟩ := by
            ext
            dsimp
            omega
          split
          · exfalso
            rename_i h₅
            simp only [h₆, symm_apply_apply, Fin.lt_def] at h₅
            omega
          · rename_i h₅
            simp only [h₆, symm_apply_apply, Fin.ext_iff]
            omega
      · simp only [PermFinPadAt_core, h₂, false_and, ↓reduceDIte, Nat.gt_of_not_le h₂]
        split
        · rename_i h₃
          simp only [h₂, false_and]
          simp only [PermFinPadAt_core, h₂, false_and, ↓reduceDIte, Nat.gt_of_not_le h₂, h₃] at h₁
          omega
        · rename_i h₃
          simp only [PermFinPadAt_core, h₂, Nat.gt_of_not_le h₂, h₃, false_and, ↓reduceDIte] at h₁
          dsimp
          generalize_proofs pf1 pf2 pf3 pf4
          have h₄ : (⟨(p ⟨↑x, pf1⟩) + n - 1 - (n - 1), pf2⟩ : Fin m) = p ⟨↑x, pf1⟩ := by
            ext
            dsimp
            omega
          simpa [h₄] using fun h ↦ (h₂ h).elim

/-- PermfindPadAt takes the permutation in Sm and "expands" location k out of m, into a block
 of n indices that get permuted together, and creates a perm of length (m+n-1).-/
@[irreducible]
def PermFinPadAt {n m : ℕ} (p : Perm (Fin m)) (hn : 0 < n) (k : Fin m) : Perm (Fin (m+n-1)) :=
  ⟨PermFinPadAt_core p hn k, PermFinPadAt_core p.symm hn (p k),
    PermFinPadAt_core.LeftInverse p hn k,
  by
    apply Function.LeftInverse.rightInverse_of_card_le (PermFinPadAt_core.LeftInverse p hn k)
    simp only [Fintype.card_fin, le_refl]⟩

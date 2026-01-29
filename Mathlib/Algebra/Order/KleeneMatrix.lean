/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Data.Matrix.Block

/-!
# Kleene algebras over matrices
-/

@[expose] public section

namespace Matrix

variable {α ι : Type*} [KleeneAlgebra α]

open Computability

structure KleeneMatrix n K where ofMatrix :: toMatrix : Matrix n n K

#check KleeneMatrix.ofMatrix
#check KleeneMatrix.toMatrix

/-variable [KleeneAlgebra (Matrix m m α)] [KleeneAlgebra (Matrix n n α)]

instance instKleeneAlgebraSum
    (o₁ : ∀ M₁ M₂ : Matrix m m α, M₁ ≤ M₂ ↔ (M₁ · ·) ≤ (M₂ · ·))
    (o₂ : ∀ M₁ M₂ : Matrix n n α, M₁ ≤ M₂ ↔ (M₁ · ·) ≤ (M₂ · ·)) :
    KleeneAlgebra (Matrix (m ⊕ n) (m ⊕ n) α) where
  le A B := (A · ·) ≤ (B · ·)
  le_refl _ := by rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ h₂ := by
    ext i j
    exact le_antisymm (h₁ i j) (h₂ i j)
  le_sup_left _ _ _ _ := by simp
  le_sup_right _ _ _ _ := by simp
  sup_le _ _ _ h₁ h₂ i j := by simp [h₁ i j, h₂ i j]
  bot_le _ _ _ := by simp
  kstar M :=
    let A := M.toBlocks₁₁
    let B := M.toBlocks₁₂
    let C := M.toBlocks₂₁
    let D := M.toBlocks₂₂
    let F := A + B * D∗ * C
    let B' := F∗ * B * D∗
    let C' := D∗ * C * F∗
    let D' := D∗ + D∗ * C * F∗ * B * D∗
    fromBlocks F∗ B' C' D'
  one_le_kstar E := by
    extract_lets A B C D F B' C' D'
    rw [← fromBlocks_one]
    rintro (i | i) (j | j)
    · simp only [fromBlocks_apply₁₁]
      sorry
    · simp
    · simp
    · simp only [fromBlocks_apply₂₂]
      sorry
  mul_kstar_le_kstar E := by
    sorry
  kstar_mul_le_kstar E := by
    sorry
  mul_kstar_le_self X E h := by
    sorry
  kstar_mul_le_self X E h := by
    sorry
-/

/-instance instKleeneAlgebraFinZero : KleeneAlgebra (Matrix (Fin 0) (Fin 0) α) where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  le_antisymm _ _ _ _ := ext_of_mulVec_single fun _ ↦ rfl
  le_sup_left _ _ := trivial
  le_sup_right _ _ := trivial
  sup_le _ _ _ _ _ := trivial
  bot_le _ := trivial
  kstar := id
  one_le_kstar _ := trivial
  mul_kstar_le_kstar _ := trivial
  kstar_mul_le_kstar _ := trivial
  mul_kstar_le_self _ _ _ := trivial
  kstar_mul_le_self _ _ _ := trivial

instance instKleeneAlgebraFinOne : KleeneAlgebra (Matrix (Fin 1) (Fin 1) α) where
  le A B := A 0 0 ≤ B 0 0
  le_refl _ := by rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ h₂ := by
    ext i j
    rw [i.fin_one_eq_zero, j.fin_one_eq_zero]
    exact le_antisymm h₁ h₂
  le_sup_left _ _ := by simp
  le_sup_right _ _ := by simp
  sup_le _ _ _ h₁ h₂ := by simp [h₁, h₂]
  bot_le := by simp
  kstar A := A.map (·∗)
  one_le_kstar _ := by simp
  mul_kstar_le_kstar _ := by simpa [mul_apply] using mul_kstar_le_kstar
  kstar_mul_le_kstar _ := by simpa [mul_apply] using kstar_mul_le_kstar
  mul_kstar_le_self _ _ h := by
    simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton] at *
    exact mul_kstar_le_self h
  kstar_mul_le_self _ _ h := by
    simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton] at *
    exact kstar_mul_le_self h
-/

end Matrix

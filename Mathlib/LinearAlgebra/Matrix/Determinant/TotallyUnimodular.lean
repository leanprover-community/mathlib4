/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Vladimir Kolmogorov, Ivan Sergeev
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Totally unimodular matrices

This file defines totally unimodular matrices and provides basic API for them.

## Main definitions

 - `Matrix.IsTotallyUnimodular`: a matrix is totally unimodular iff every square submatrix
    (not necessarily contiguous) has determinant `0` or `1` or `-1`.

## Main results

 - `Matrix.isTotallyUnimodular_iff`: a matrix is totally unimodular iff every square submatrix
    (possibly with repeated rows and/or repeated columns) has determinant `0` or `1` or `-1`.
 - `Matrix.IsTotallyUnimodular.apply`: entry in a totally unimodular matrix is `0` or `1` or `-1`.

-/

namespace Matrix

variable {m n R : Type*} [CommRing R]

/-- Is the matrix `A` totally unimodular? -/
def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det = 0 ∨
    (A.submatrix f g).det = 1 ∨
    (A.submatrix f g).det = -1

lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n,
      (A.submatrix f g).det = 0 ∨
      (A.submatrix f g).det = 1 ∨
      (A.submatrix f g).det = -1 := by
  constructor <;> intro hA
  · intro k f g
    if hf : f.Injective then
      if hg : g.Injective then
        exact hA k f g hf hg
      else
        left
        unfold Function.Injective at hg
        push_neg at hg
        obtain ⟨i, j, hqij, hij⟩ := hg
        apply Matrix.det_zero_of_column_eq hij
        intro
        simp [hqij]
    else
      left
      unfold Function.Injective at hf
      push_neg at hf
      obtain ⟨i, j, hpij, hij⟩ := hf
      apply Matrix.det_zero_of_row_eq
      · exact hij
      show (A (f i)) ∘ (g ·) = (A (f j)) ∘ (g ·)
      rw [hpij]
  · intro _ _ _ _ _
    apply hA

lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular)
    (i : m) (j : n) :
    A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
  let f : Fin 1 → m := (fun _ => i)
  let g : Fin 1 → n := (fun _ => j)
  convert hA 1 f g (Function.injective_of_subsingleton f) (Function.injective_of_subsingleton g) <;>
  exact (det_fin_one (A.submatrix f g)).symm

lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (hA : A.IsTotallyUnimodular) {k : ℕ}
    (f : Fin k → m) (g : Fin k → n) :
    (A.submatrix f g).IsTotallyUnimodular := by
  intro _ _ _ _ _
  rw [Matrix.submatrix_submatrix]
  rw [Matrix.isTotallyUnimodular_iff] at hA
  apply hA

lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  intro _ _ _ _ _
  simp only [← Matrix.transpose_submatrix, Matrix.det_transpose]
  apply hA <;> assumption

lemma mapEquiv_IsTotallyUnimodular {X' Y' : Type*} (A : Matrix m n R) (eX : X' ≃ m) (eY : Y' ≃ n) :
    Matrix.IsTotallyUnimodular ((A · ∘ eY) ∘ eX) ↔ A.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff, Matrix.isTotallyUnimodular_iff]
  constructor <;> intro hA k f g
  · simpa [Matrix.submatrix] using hA k (eX.symm ∘ f) (eY.symm ∘ g)
  · simpa [Matrix.submatrix] using hA k (eX ∘ f) (eY ∘ g)

end Matrix

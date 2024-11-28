/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Vladimir Kolmogorov, Ivan Sergeev
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Sign

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

/-- `A.IsTotallyUnimodular` means that every square submatrix of `A` (not necessarily contiguous)
has determinant `0` or `1` or `-1`; that is, the determinant is in the range of `SignType.cast`. -/
def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast

lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  constructor <;> intro hA
  · intro k f g
    by_cases h : f.Injective ∧ g.Injective
    · exact hA k f g h.1 h.2
    · refine ⟨0, ?_⟩
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at h
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := h
      · rw [← det_transpose, transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro _ _ _ _ _
    apply hA

lemma isTotallyUnimodular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι], ∀ f : ι → m, ∀ g : ι → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA

lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular)
    (i : m) (j : n) :
    A i j ∈ Set.range SignType.cast := by
  let f : Fin 1 → m := (fun _ => i)
  let g : Fin 1 → n := (fun _ => j)
  convert hA 1 f g (Function.injective_of_subsingleton f) (Function.injective_of_subsingleton g)
  exact (det_fin_one (A.submatrix f g)).symm

lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (hA : A.IsTotallyUnimodular) {k : ℕ}
    (f : Fin k → m) (g : Fin k → n) :
    (A.submatrix f g).IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

lemma transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply IsTotallyUnimodular.transpose

lemma mapEquiv_isTotallyUnimodular {X' Y' : Type*} (A : Matrix m n R) (eX : X' ≃ m) (eY : Y' ≃ n) :
    IsTotallyUnimodular ((A · ∘ eY) ∘ eX) ↔ A.IsTotallyUnimodular := by
  rw [isTotallyUnimodular_iff, isTotallyUnimodular_iff]
  constructor <;> intro hA k f g
  · simpa [submatrix] using hA k (eX.symm ∘ f) (eY.symm ∘ g)
  · simpa [submatrix] using hA k (eX ∘ f) (eY ∘ g)

lemma fromRows_row0_isTotallyUnimodular_iff (A : Matrix m n R) {m' : Type*} :
    (fromRows A (row m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [isTotallyUnimodular_iff, isTotallyUnimodular_iff]
  constructor <;> intro hA k f g
  · exact hA k (Sum.inl ∘ f) g
  · if zerow : ∃ i, ∃ x', f i = Sum.inr x' then
      obtain ⟨i, _, _⟩ := zerow
      use 0
      rw [eq_comm]
      apply det_eq_zero_of_row_eq_zero i
      intro
      simp_all
    else
      obtain ⟨_, rfl⟩ : ∃ f₀ : Fin k → m, f = Sum.inl ∘ f₀ := by
        have hi (i : Fin k) : ∃ x, f i = Sum.inl x :=
          match hfi : f i with
          | .inl x => ⟨x, rfl⟩
          | .inr x => (zerow ⟨i, x, hfi⟩).elim
        choose f₀ hf₀ using hi
        use f₀
        ext
        apply hf₀
      apply hA

lemma fromColumns_col0_isTotallyUnimodular_iff (A : Matrix m n R) {n' : Type*} :
    (fromColumns A (col n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromColumns, transpose_col,
    fromRows_row0_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

end Matrix

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

variable {m m' n n' R : Type*} [CommRing R]

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

lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n) :
    A i j ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff] at hA
  convert hA 1 (fun _ => i) (fun _ => j)
  simp

lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (f : m' → m) (g : n' → n)
    (hA : A.IsTotallyUnimodular) :
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

lemma IsTotallyUnimodular.reindex {A : Matrix m n R} (eX : m ≃ m') (eY : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    IsTotallyUnimodular (A.reindex eX eY) :=
  hA.submatrix _ _

lemma reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    IsTotallyUnimodular (A.reindex em en) ↔ A.IsTotallyUnimodular := by
  rw [isTotallyUnimodular_iff, isTotallyUnimodular_iff]
  constructor <;> intro hA k f g
  · simpa [submatrix] using hA k (em ∘ f) (en ∘ g)
  · simpa [submatrix] using hA k (em.symm ∘ f) (en.symm ∘ g)

-- TODO: move
lemma neg_one_pow_mem_signType_range (n : ℕ) {a : R} (ha : a ∈ Set.range SignType.cast) :
    (-1 : R) ^ n * a ∈ Set.range SignType.cast := by
  let S := MonoidHom.mrange (SignType.castHom (α := R)).toMonoidHom
  refine mul_mem (s := S) (pow_mem ?_ _) ha
  exact ⟨-1, by rfl⟩

/--
If `A` is totally unimodular and each row of B is all zeros except for at most a single 1,
then `fromRows A B` is totally unimodular.
-/
lemma IsTotallyUnimodular.fromRows_one_aux [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : ∀ i : m', B i = 0 ∨ ∃ j, B i = Function.update (0 : n → R) j 1)
    (hA : A.IsTotallyUnimodular) :
    (fromRows A B).IsTotallyUnimodular := by
  intro k f g hf hg
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    by_cases hfr : ∃ i : Fin (k + 1), (f i).isRight
    · simp only [Sum.isRight_iff] at hfr
      obtain ⟨i, j, hfi⟩ := hfr
      have hAB := det_succ_row ((A.fromRows B).submatrix f g) i
      simp only [submatrix_apply, hfi, fromRows_apply_inr] at hAB
      obtain (hj | ⟨j', hj'⟩) := hB j
      · use 0
        simpa [hj] using hAB.symm
      · simp only [hj', Function.update_apply] at hAB
        by_cases hj'' : ∃ x, g x = j'
        · obtain ⟨x, rfl⟩ := hj''
          simp only [Nat.succ_eq_add_one, hg.eq_iff, Pi.zero_apply, mul_ite, mul_one, mul_zero,
            submatrix_submatrix, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ] at hAB
          rw [hAB]
          apply neg_one_pow_mem_signType_range
          exact ih _ _
            (hf.comp Fin.succAbove_right_injective)
            (hg.comp Fin.succAbove_right_injective)
        · simp only [not_exists] at hj''
          use 0
          simpa [hj''] using hAB.symm
    · simp only [not_exists, Bool.not_eq_true, Sum.isRight_eq_false, Sum.isLeft_iff] at hfr
      choose f' hf' using hfr
      rw [isTotallyUnimodular_iff] at hA
      simp only [funext hf']
      exact hA (k + 1) f' g

/--
If `A` is totally unimodular and each row of B is all zeros except for at most a single 1,
then `fromRows A B` is totally unimodular.
-/
lemma fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : ∀ i : m', B i = 0 ∨ ∃ j, B i = Function.update (0 : n → R) j 1) :
    (fromRows A B).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨.submatrix Sum.inl id, .fromRows_one_aux hB⟩

lemma fromRows_one_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows A (1 : Matrix n n R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  fromRows_isTotallyUnimodular_iff_rows <| fun i ↦ Or.inr
    ⟨i, funext fun j ↦ by simp [one_apply, Function.update_apply, eq_comm]⟩

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff

lemma fromRows_row0_isTotallyUnimodular_iff (A : Matrix m n R) {m' : Type*} :
    (fromRows A (row m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  classical
  exact fromRows_isTotallyUnimodular_iff_rows (by aesop)

lemma fromColumns_col0_isTotallyUnimodular_iff (A : Matrix m n R) {n' : Type*} :
    (fromColumns A (col n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromColumns, transpose_col,
    fromRows_row0_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

end Matrix

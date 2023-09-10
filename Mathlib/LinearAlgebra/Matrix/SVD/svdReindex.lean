/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Rank

/-! # Reindexing using Non-zero/Zero Partition Eigenvalues of AAᴴ and AᴴA

Given a Fin M × Fin N we wish to define equivlances that allow us to move between the following
representaions smoothly. Let R be the rank
  Fin N ≃ (Fin R ⊕ Fin (N - R)) which can be achievd through
  Fin N ≃ {Non-zero Eigs} ⊕ (Zero Eigs) ≃ Fin R ⊕ Fin (N - R)

  Fin M ≃ (Fin R ⊕ Fin (M - R)) which can be achievd through
  Fin M ≃ {Non-zero Eigs} ⊕ (Zero Eigs) ≃ Fin R ⊕ Fin (M - R)

  Note that we know R ≤ MIN(M, N) -/
variable {𝕂: Type}[IsROrC 𝕂][DecidableEq 𝕂]
variable {M N: ℕ}

open Matrix BigOperators

namespace Matrix

open scoped ComplexOrder

lemma rank_eq_card_pos_eigs_conj_transpose_mul_self (A: Matrix (Fin M) (Fin N) 𝕂) :
    A.rank = Fintype.card {i // (isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} := by
  rw[← rank_conjTranspose_mul_self, IsHermitian.rank_eq_card_non_zero_eigs]

lemma rank_eq_card_pos_eigs_self_mul_conj_transpose (A: Matrix (Fin M) (Fin N) 𝕂) :
    A.rank = Fintype.card {i // (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} := by
  rw[← rank_self_mul_conjTranspose, IsHermitian.rank_eq_card_non_zero_eigs]

/-- For matrix A of size m × n and rank A.rank : we have an equivalence relation between elements of
Fin (A.rank) and the set non-zero eigenvalues of the matrix Aᴴ⬝A -/
noncomputable def fin_rank_equiv_eigs_conjTranspose_mul_self (A: Matrix (Fin M) (Fin N) 𝕂) :
    {i // (isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} ≃ Fin (A.rank) :=
  (Fintype.equivFinOfCardEq (rank_eq_card_pos_eigs_conj_transpose_mul_self A).symm)

/-- For matrix A of size m × n and rank A.rank : we have an equivalence relation between elements of
Fin (A.rank) and the set non-zero eigenvalues of the matrix A⬝Aᴴ -/
noncomputable def fin_rank_equiv_eigs_mul_conjTranspose (A: Matrix (Fin M) (Fin N) 𝕂) :
    {i // (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃ Fin (A.rank) :=
  (Fintype.equivFinOfCardEq (rank_eq_card_pos_eigs_self_mul_conj_transpose A).symm)

/-- For matrix of size m × n nad rank A.rank : we have an equivalence relation between the elements
of Fin (width) and the eigevalues of the matrix Aᴴ⬝A partitioned into
- non-zero eigenvaules: (exactly A.rank) of them see `fin_rank_equiv_eigs_conjTranspose_mul_self`
- zero eigenvaules: (exactly width - A.rank) of them -/
noncomputable def equiv_fin_width_eigs_conjTranspose_mul_self (A: Matrix (Fin M) (Fin N) 𝕂) :
    (Fin N) ≃ (Fin A.rank) ⊕ (Fin (N - A.rank)) := by
  let em := Equiv.sumCompl (fun i =>  (isHermitian_transpose_mul_self A).eigenvalues i ≠ 0)
  let eₙᵣ : {i // ¬(isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} ≃ Fin (N - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_conj_transpose_mul_self]
  exact Equiv.trans em.symm  (Equiv.sumCongr (fin_rank_equiv_eigs_conjTranspose_mul_self A) eₙᵣ)

/-- For matrix of size m × n nad rank A.rank : we have an equivalence relation between the elements
of Fin (height) and the eigevalues of the matrix A⬝Aᴴ partitioned into
- non-zero eigenvaules: (exactly A.rank) of them see `fin_rank_equiv_eigs_mul_conjTranspose`
- zero eigenvaules: (exactly height - A.rank) of them -/
noncomputable def equiv_fin_height_eigs_mul_conjTranspose (A: Matrix (Fin M) (Fin N) 𝕂) :
    (Fin M) ≃ (Fin A.rank) ⊕ (Fin (M - A.rank)) := by
  let em := Equiv.sumCompl (fun i =>  (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0)
  let eᵣ' : {i // (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃ Fin A.rank := by
    apply Fintype.equivFinOfCardEq
    rw [rank_eq_card_pos_eigs_self_mul_conj_transpose]
  let eₘᵣ : {i // ¬(isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃
    Fin (M - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_self_mul_conj_transpose]
  exact Equiv.trans em.symm  (Equiv.sumCongr eᵣ' eₘᵣ)

/-- When the eigenvalues of the matrix Aᴴ⬝A are partitioned using
`equiv_fin_width_eigs_conjTranspose_mul_self` i.e. into non-zero and zero eigenvalues, any element
from the second partition is obivuosly zero! -/
lemma enz_nr_zero (A: Matrix (Fin M) (Fin N) 𝕂) (i: Fin (N - A.rank)):
  (isHermitian_transpose_mul_self A).eigenvalues
    ((equiv_fin_width_eigs_conjTranspose_mul_self A).symm (Sum.inr i)) = 0 := by
  unfold equiv_fin_width_eigs_conjTranspose_mul_self Equiv.sumCongr
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    Equiv.sumCompl_apply_inr]
  let eₙᵣ : {i // ¬(isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} ≃ Fin (N - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_conj_transpose_mul_self]
  exact Iff.mp Function.nmem_support ((eₙᵣ.symm i).prop)

/-- When the eigenvalues of the matrix A⬝Aᴴ are partitioned using
`equiv_fin_height_eigs_mul_conjTranspose` i.e. into non-zero and zero eigenvalues, any element from
the second partition is obivuosly zero! -/
lemma emz_mr_zero (A: Matrix (Fin M) (Fin N) 𝕂) (i: Fin (M - A.rank)) :
    (isHermitian_mul_conjTranspose_self A).eigenvalues
      ((equiv_fin_height_eigs_mul_conjTranspose A).symm (Sum.inr i)) = 0 := by
  unfold equiv_fin_height_eigs_mul_conjTranspose Equiv.sumCongr
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    Equiv.sumCompl_apply_inr]
  let eₘᵣ : {i // ¬(isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃
    Fin (M - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_self_mul_conj_transpose]
  exact Iff.mp Function.nmem_support ((eₘᵣ.symm i).prop)

lemma enz_inj (A: Matrix (Fin M) (Fin N) 𝕂) (i j: Fin (N - A.rank)) :
    ¬ (i = j) → (equiv_fin_width_eigs_conjTranspose_mul_self A).symm (Sum.inr i) ≠
      (equiv_fin_width_eigs_conjTranspose_mul_self A).symm (Sum.inr j) := by
  intros h
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, h]

lemma emz_inj (A: Matrix (Fin M) (Fin N) 𝕂) (i j: Fin (M - A.rank)) :
    ¬ (i = j) → (equiv_fin_height_eigs_mul_conjTranspose A).symm (Sum.inr i) ≠
      (equiv_fin_height_eigs_mul_conjTranspose A).symm (Sum.inr j) := by
  intros h
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, h]


end Matrix

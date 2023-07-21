/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SVD.IsROrCStarOrderedRing
import Mathlib.LinearAlgebra.Matrix.SVD.RankMulIsUnit
import Mathlib.LinearAlgebra.Matrix.SVD.HermitianMatricesRank

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

noncomputable def er (A: Matrix (Fin M) (Fin N) 𝕂) :
  {i // (isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} ≃ Fin (A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [rank_eq_card_pos_eigs_conj_transpose_mul_self]

noncomputable def er' (A: Matrix (Fin M) (Fin N) 𝕂) :
  {i // (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃ Fin (A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [rank_eq_card_pos_eigs_self_mul_conj_transpose]

noncomputable def enz (A: Matrix (Fin M) (Fin N) 𝕂) : (Fin N) ≃ (Fin A.rank) ⊕ (Fin (N - A.rank))
  := by
  let em := Equiv.sumCompl (fun i =>  (isHermitian_transpose_mul_self A).eigenvalues i ≠ 0)
  let eₙᵣ : {i // ¬(isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} ≃ Fin (N - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_conj_transpose_mul_self]
  exact Equiv.trans em.symm  (Equiv.sumCongr (er A) eₙᵣ)

noncomputable def emz (A: Matrix (Fin M) (Fin N) 𝕂) : (Fin M) ≃ (Fin A.rank) ⊕ (Fin (M - A.rank))
  := by
  let em := Equiv.sumCompl (fun i =>  (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0)
  let eᵣ' : {i // (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃ Fin A.rank := by
    apply Fintype.equivFinOfCardEq
    rw [rank_eq_card_pos_eigs_self_mul_conj_transpose]
  let eₘᵣ : {i // ¬(isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃
    Fin (M - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_self_mul_conj_transpose]
  exact Equiv.trans em.symm  (Equiv.sumCongr eᵣ' eₘᵣ)

lemma enz_nr_zero (A: Matrix (Fin M) (Fin N) 𝕂) (i: Fin (N - A.rank)):
  (isHermitian_transpose_mul_self A).eigenvalues ((enz A).symm (Sum.inr i)) = 0 := by
  unfold enz Equiv.sumCongr
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    Equiv.sumCompl_apply_inr]
  let eₙᵣ : {i // ¬(isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} ≃ Fin (N - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_conj_transpose_mul_self]
  exact Iff.mp Function.nmem_support ((eₙᵣ.symm i).prop)

lemma emz_mr_zero (A: Matrix (Fin M) (Fin N) 𝕂) (i: Fin (M - A.rank)):
  (isHermitian_mul_conjTranspose_self A).eigenvalues ((emz A).symm (Sum.inr i)) = 0 := by
  unfold emz Equiv.sumCongr
  simp only [ne_eq, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk, Sum.elim_inr,
    Equiv.sumCompl_apply_inr]
  let eₘᵣ : {i // ¬(isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} ≃
    Fin (M - A.rank) := by
    apply Fintype.equivFinOfCardEq
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rank_eq_card_pos_eigs_self_mul_conj_transpose]
  exact Iff.mp Function.nmem_support ((eₘᵣ.symm i).prop)

lemma enz_inj (A: Matrix (Fin M) (Fin N) 𝕂) (i j: Fin (N - A.rank)):
  ¬ (i = j) → (enz A).symm (Sum.inr i) ≠ (enz A).symm (Sum.inr j) := by
  intros h
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, h]

lemma emz_inj (A: Matrix (Fin M) (Fin N) 𝕂) (i j: Fin (M - A.rank)):
  ¬ (i = j) → (emz A).symm (Sum.inr i) ≠ (emz A).symm (Sum.inr j) := by
  intros h
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, h]


end Matrix

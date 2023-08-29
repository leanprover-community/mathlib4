/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Matrix.CharP

#align_import linear_algebra.matrix.charpoly.finite_field from "leanprover-community/mathlib"@"b95b8c7a484a298228805c72c142f6b062eb0d70"

/-!
# Results on characteristic polynomials and traces over finite fields.
-/


noncomputable section

open Polynomial Matrix

open scoped Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]

@[simp]
theorem FiniteField.Matrix.charpoly_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    (M ^ Fintype.card K).charpoly = M.charpoly := by
  cases (isEmpty_or_nonempty n).symm
  -- ⊢ charpoly (M ^ Fintype.card K) = charpoly M
  · cases' CharP.exists K with p hp; letI := hp
    -- ⊢ charpoly (M ^ Fintype.card K) = charpoly M
                                     -- ⊢ charpoly (M ^ Fintype.card K) = charpoly M
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    -- ⊢ charpoly (M ^ Fintype.card K) = charpoly M
    haveI : Fact p.Prime := ⟨hp⟩
    -- ⊢ charpoly (M ^ Fintype.card K) = charpoly M
    dsimp at hk; rw [hk]
    -- ⊢ charpoly (M ^ Fintype.card K) = charpoly M
                 -- ⊢ charpoly (M ^ p ^ k) = charpoly M
    apply (frobenius_inj K[X] p).iterate k
    -- ⊢ (↑(frobenius K[X] p))^[k] (charpoly (M ^ p ^ k)) = (↑(frobenius K[X] p))^[k] …
    repeat' rw [iterate_frobenius (R := K[X])]; rw [← hk]
    -- ⊢ charpoly (M ^ Fintype.card K) ^ Fintype.card K = charpoly M ^ Fintype.card K
    rw [← FiniteField.expand_card]
    -- ⊢ ↑(expand K (Fintype.card K)) (charpoly (M ^ Fintype.card K)) = charpoly M ^  …
    unfold charpoly
    -- ⊢ ↑(expand K (Fintype.card K)) (det (charmatrix (M ^ Fintype.card K))) = det ( …
    rw [AlgHom.map_det, ← coe_detMonoidHom, ← (detMonoidHom : Matrix n n K[X] →* K[X]).map_pow]
    -- ⊢ ↑detMonoidHom (↑(AlgHom.mapMatrix (expand K (Fintype.card K))) (charmatrix ( …
    apply congr_arg det
    -- ⊢ ↑(AlgHom.mapMatrix (expand K (Fintype.card K))) (charmatrix (M ^ Fintype.car …
    refine' matPolyEquiv.injective _
    -- ⊢ ↑matPolyEquiv (↑(AlgHom.mapMatrix (expand K (Fintype.card K))) (charmatrix ( …
    rw [AlgEquiv.map_pow, matPolyEquiv_charmatrix, hk, sub_pow_char_pow_of_commute, ← C_pow]
    -- ⊢ ↑matPolyEquiv (↑(AlgHom.mapMatrix (expand K (p ^ k))) (charmatrix (M ^ p ^ k …
    · exact (id (matPolyEquiv_eq_x_pow_sub_c (p ^ k) M) : _)
      -- 🎉 no goals
    · exact (C M).commute_X
      -- 🎉 no goals
  · exact congr_arg _ (Subsingleton.elim _ _)
    -- 🎉 no goals
#align finite_field.matrix.charpoly_pow_card FiniteField.Matrix.charpoly_pow_card

@[simp]
theorem ZMod.charpoly_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    (M ^ p).charpoly = M.charpoly := by
  have h := FiniteField.Matrix.charpoly_pow_card M
  -- ⊢ charpoly (M ^ p) = charpoly M
  rwa [ZMod.card] at h
  -- 🎉 no goals
#align zmod.charpoly_pow_card ZMod.charpoly_pow_card

theorem FiniteField.trace_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    trace (M ^ Fintype.card K) = trace M ^ Fintype.card K := by
  cases isEmpty_or_nonempty n
  -- ⊢ trace (M ^ Fintype.card K) = trace M ^ Fintype.card K
  · simp [Matrix.trace]; rw [zero_pow Fintype.card_pos]
    -- ⊢ 0 = 0 ^ Fintype.card K
                         -- 🎉 no goals
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
    FiniteField.Matrix.charpoly_pow_card, FiniteField.pow_card]
#align finite_field.trace_pow_card FiniteField.trace_pow_card

theorem ZMod.trace_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    trace (M ^ p) = trace M ^ p := by have h := FiniteField.trace_pow_card M; rwa [ZMod.card] at h
                                      -- ⊢ trace (M ^ p) = trace M ^ p
                                                                              -- 🎉 no goals
#align zmod.trace_pow_card ZMod.trace_pow_card

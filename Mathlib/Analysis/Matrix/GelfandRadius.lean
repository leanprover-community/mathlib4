/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius

/-!
# Golfand radius of matrices

This file proves results on the Gelfand radius of matrices.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

variable {R m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [SeminormedCommRing R]

open Filter Topology in
theorem Matrix.gelfandRadius_conj_le
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hCA : C * A = 1) : gelfandRadius (A * B * C) ≤ gelfandRadius B := by
  by_cases! hB : ‖B‖ ≤ 0
  · rw [gelfandRadius_of_norm_le_zero, gelfandRadius_of_norm_le_zero hB]
    grw [Matrix.linfty_opNorm_mul, Matrix.linfty_opNorm_mul, hB, mul_zero, zero_mul]
  replace hB : 0 < ‖(1 : Matrix n n R)‖ := by
    contrapose! hB
    grw [← mul_one B, linfty_opNorm_mul, hB, mul_zero]
  have h k (hk : 1 ≤ k) : (A * B * C) ^ k = A * B ^ k * C := by
    refine Nat.le_induction (by simp) (fun k _ ih ↦ ?_) k hk
    transitivity A * B ^ k * (C * A) * B * C <;> grind [Matrix.mul_assoc]
  have key {c : ℝ} (hc : c ≠ 0) : Tendsto (fun n : ℕ ↦ c ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
    ((c.continuous_const_rpow hc).tendsto' 0 1 c.rpow_zero).comp tendsto_inv_atTop_nhds_zero_nat
  grw [← hCA, linfty_opNorm_mul] at hB
  have hA : 0 < ‖A‖ := pos_of_mul_pos_right hB (norm_nonneg C)
  have hC : 0 < ‖C‖ := pos_of_mul_pos_left hB (norm_nonneg A)
  replace key := ((key hA.ne').mul (tendsto_gelfandRadius B)).mul (key hC.ne')
  rw [one_mul, mul_one] at key
  refine le_of_tendsto_of_tendsto' (tendsto_gelfandRadius (A * B * C)) key fun k ↦ ?_
  rcases eq_zero_or_pos k with rfl | hk
  · simp
  · grw [h k hk, Matrix.linfty_opNorm_mul, Matrix.linfty_opNorm_mul,
      Real.mul_rpow, Real.mul_rpow] <;> positivity

theorem Matrix.gelfandRadius_conj
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hAC : A * C = 1) (hCA : C * A = 1) : gelfandRadius (A * B * C) = gelfandRadius B := by
  refine le_antisymm (Matrix.gelfandRadius_conj_le A B C hCA) ?_
  grw [← gelfandRadius_conj_le C (A * B * C) A hAC, Matrix.mul_assoc, Matrix.mul_assoc,
    hCA, Matrix.mul_one, ← Matrix.mul_assoc, hCA, Matrix.one_mul]

theorem map_finset_sup'' {α β ι : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (f : α → β) (h : ∀ x y, f (x ⊔ y) = f x ⊔ f y) {s : Finset ι} (hs) (g : ι → α) :
    f (s.sup' hs g) = s.sup' hs (f ∘ g) := by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

theorem Matrix.gelfandRadius_blockDiagonal_eq_sup (M : n → Matrix m m R) [Nonempty n] :
    gelfandRadius (Matrix.blockDiagonal M) = ⨆ i, gelfandRadius (M i) := by
  let s : Finset n := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  rw [← Finset.sup'_univ_eq_ciSup]
  refine tendsto_nhds_unique_of_forall (tendsto_gelfandRadius (blockDiagonal M))
    (Filter.Tendsto.finset_sup'_nhds_apply hs fun i hi ↦ tendsto_gelfandRadius (M i)) fun k ↦ ?_
  suffices ‖blockDiagonal M ^ k‖₊ ^ (k : ℝ)⁻¹ = s.sup' hs fun x ↦ ‖M x ^ k‖₊ ^ (k : ℝ)⁻¹ by
    rw [← coe_nnnorm, ← NNReal.coe_rpow, this, Finset.sup'_univ_eq_ciSup, Finset.sup'_univ_eq_ciSup]
    simp
  have key : ‖blockDiagonal M ^ k‖₊ ^ (k : ℝ)⁻¹ = (s.sup' hs (‖M · ^ k‖₊)) ^ (k : ℝ)⁻¹ := by
    rw [← blockDiagonal_pow, linfty_opNNNorm_blockDiagonal, Pi.pow_def, Pi.nnnorm_def,
      Finset.sup_univ_eq_ciSup, Finset.sup'_univ_eq_ciSup]
  have key : ‖blockDiagonal M ^ k‖₊ ^ (k : ℝ)⁻¹ = s.sup' hs (‖M · ^ k‖₊ ^ (k : ℝ)⁻¹) := by
    rw [key]
    apply map_finset_sup'' (fun x : NNReal ↦ x ^ (k : ℝ)⁻¹) (fun x y ↦ ?_) hs
    rw [← NNReal.coe_inj]
    simp only [NNReal.coe_rpow, NNReal.coe_max]
    apply Real.rpow_max <;> positivity
  exact key

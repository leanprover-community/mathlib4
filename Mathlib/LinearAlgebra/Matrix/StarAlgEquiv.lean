/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# ⋆-algebra equivalences on matrices

This file shows that ⋆-algebra equivalences on matrices are unitarily inner.
-/

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open Matrix
open scoped ComplexOrder

/-- A ⋆-algebra equivalence on matrices is unitarily inner, i.e., there exists a unitary matrix `U`
such that `f x = U * x * star U`. -/
theorem Matrix.StarAlgEquiv.coe_eq_unitaryGroup_conjugate
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : ∃ U : unitaryGroup n 𝕜,
    ⇑f = fun x => U * x * (star U : Matrix n n 𝕜) := by
  obtain hn | hn := isEmpty_or_nonempty n
  · exact ⟨1, funext fun a => Matrix.ext fun i => isEmpty_iff.mp hn i |>.elim⟩
  let f' := f.toAlgEquiv
  obtain ⟨y, hy⟩ := f'.coe_eq_generalLinearGroup_conjugate
  let y' := (y : Matrix n n 𝕜)
  have hf (x : Matrix n n 𝕜) : f' x = y' * x * y'⁻¹ := by simp [y', ← coe_units_inv, hy]
  replace hf (x : Matrix n n 𝕜) : f x = y' * x * y'⁻¹ := hf _ ▸ rfl
  have (x : Matrix n n 𝕜) : (f x)ᴴ = f xᴴ := map_star _ _ |>.symm
  simp_rw [hf, conjTranspose_mul, conjTranspose_nonsing_inv] at this
  replace this (x : Matrix n n 𝕜) : y'ᴴ * y' * xᴴ * y'⁻¹ = xᴴ * y'ᴴ := by
    simp_rw [mul_assoc, ← mul_assoc y', ← this, ← mul_assoc,
      ← conjTranspose_nonsing_inv, ← conjTranspose_mul, inv_mul_of_invertible, mul_one]
  replace this (x : Matrix n n 𝕜) : Commute x (y'ᴴ * y') := by
    simp_rw [Commute, SemiconjBy, ← mul_assoc, ← (conjTranspose_conjTranspose x ▸ this xᴴ),
      mul_assoc, inv_mul_of_invertible, mul_one]
  simp_rw [Commute, SemiconjBy, ← Semigroup.mem_center_iff, center_eq_range] at this
  obtain ⟨α, hα⟩ := this
  have this : IsUnit (y'ᴴ * y') := isUnit_iff_exists.mpr ⟨y'⁻¹ * y'⁻¹ᴴ, by
    simp [← mul_assoc, mul_assoc _ _ y'ᴴ, ← conjTranspose_mul]⟩
  replace this := (PosSemidef.posDef_iff_isUnit (posSemidef_conjTranspose_mul_self _)).mpr this
  have thisα : α = RCLike.re α := by
    have this10 := IsHermitian.coe_re_diag (IsSelfAdjoint.star_mul_self y')
    simp only [star, ← hα, scalar_apply, diag_apply, diagonal_apply_eq, diag_diagonal] at this10
    have this11 : (RCLike.re α : 𝕜) • (1 : n → 𝕜) = α • 1 := by ext i; simp [congr($this10 i)]
    rwa [(smul_left_injective _ (by simp : (1 : n → 𝕜) ≠ 0)).eq_iff, eq_comm] at this11
  simp only [PosDef, ← hα, scalar_apply, ne_eq, diagonal_const_mulVec, dotProduct_smul,
    smul_eq_mul] at this
  obtain ⟨thisl, this⟩ := this
  specialize this 1 (by simp)
  have this1 : star (1 : n → 𝕜) ⬝ᵥ (1 : n → 𝕜) = (Fintype.card n : ℝ) := by simp
  rw [thisα, this1, ← RCLike.ofReal_mul, RCLike.ofReal_pos, mul_pos_iff] at this
  simp only [Nat.cast_pos, Fintype.card_pos] at this
  have this14 : ¬(Fintype.card n : ℝ) < 0 := by simp only [not_lt, Nat.cast_nonneg]
  simp_rw [this14, and_false, and_true, or_false] at this
  have isU : (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y' ∈ unitaryGroup n 𝕜 := by
    simp_rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_smul,
      RCLike.star_def, Matrix.smul_mul, Matrix.mul_smul, RCLike.conj_ofReal,
      smul_smul, ← RCLike.ofReal_mul]
    rw [← Real.rpow_add this, ← hα, thisα, scalar_apply, ← diagonal_smul]
    ext
    simp only [diagonal, RCLike.ofReal_re, one_div, Pi.smul_apply, smul_eq_mul,
      ← RCLike.ofReal_mul (K := 𝕜), ← Real.rpow_add_one (NeZero.of_pos this).out, of_apply]
    norm_num; rfl
  let U : unitaryGroup n 𝕜 := ⟨_, isU⟩
  have hU : (U : Matrix n n 𝕜) = (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y' := rfl
  have hU2 : ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y')⁻¹ = (star U : Matrix n n 𝕜) :=
    inv_eq_left_inv (by rw [← hU, UnitaryGroup.star_mul_self])
  have hU3 : ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y')⁻¹ =
      (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)⁻¹ • y'⁻¹ := by
    apply inv_eq_left_inv
    simp_rw [smul_mul, mul_smul, smul_smul]
    rw [inv_mul_cancel₀, one_smul, inv_mul_of_invertible]
    · simp [Real.rpow_eq_zero_iff_of_nonneg (le_of_lt this), (NeZero.of_pos this).out]
  use U
  ext x
  simp_rw [← hU2, hU3, hf, hU, smul_mul, mul_smul, smul_smul, ← RCLike.ofReal_inv,
    ← RCLike.ofReal_mul, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt this),
    ← Real.rpow_add this]
  norm_num

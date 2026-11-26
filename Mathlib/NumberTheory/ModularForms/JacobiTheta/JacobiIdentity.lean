/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Gareth Ma, Seewoo Lee, Wenrong Zou
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Jacobi's identity for theta functions

We prove Jacobi's identity `θ₂ ^ 4 + θ₄ ^ 4 = θ₃ ^ 4` relating the fourth powers of the Jacobi theta
functions `θ₂ = jacobiTheta₁₀`, `θ₃ = jacobiTheta` and `θ₄ = jacobiTheta₀₁`.
-/

open Complex ModularGroup ModularForm SlashInvariantForm Filter
open UpperHalfPlane hiding I

open scoped Real Topology Manifold MatrixGroups JacobiTheta

/-!
## The action of `S` and `T` on the fourth powers
-/

lemma cpow_one_half_pow_four (z : ℂ) : ((-I * z) ^ (1 / 2 : ℂ)) ^ 4 = -z ^ 2 := by
  rw [← cpow_mul_nat, (by norm_num : (1 / 2 : ℂ) * (4 : ℕ) = 2), cpow_ofNat, mul_pow, neg_sq,
    I_sq, neg_one_mul]

public theorem jacobiTheta₁₀_pow_four_slash_T :
    (fun τ : ℍ ↦ θ₂ τ ^ 4) ∣[(2 : ℤ)] T = -fun τ : ℍ ↦ θ₂ τ ^ 4 := by
  have h : cexp (π * I / 4) ^ 4 = -1 := by
    rw [← Complex.exp_natCast_mul, ← exp_pi_mul_I]
    ring_nf
  ext τ
  rw [SL_slash_apply, denom, modular_T_smul]
  simp [jacobiTheta₁₀_one_add, mul_pow, h]

public theorem jacobiTheta_pow_four_slash_T :
    (fun τ : ℍ ↦ θ₃ τ ^ 4) ∣[(2 : ℤ)] T = fun τ : ℍ ↦ θ₄ τ ^ 4 := by
  ext τ
  rw [SL_slash_apply, denom, modular_T_smul]
  simp [jacobiTheta_one_add]

public theorem jacobiTheta₀₁_pow_four_slash_T :
    (fun τ : ℍ ↦ θ₄ τ ^ 4) ∣[(2 : ℤ)] T = fun τ : ℍ ↦ θ₃ τ ^ 4 := by
  ext τ
  rw [SL_slash_apply, denom, modular_T_smul]
  simp [jacobiTheta₀₁_one_add]

public theorem jacobiTheta₁₀_pow_four_slash_S :
    (fun τ : ℍ ↦ θ₂ τ ^ 4) ∣[(2 : ℤ)] S = -fun τ : ℍ ↦ θ₄ τ ^ 4 := by
  ext τ
  simp only [SL_slash_apply, jacobiTheta₁₀_S_smul, denom_S, mul_pow, cpow_one_half_pow_four,
    Pi.neg_apply]
  field_simp [τ.ne_zero]

public theorem jacobiTheta_pow_four_slash_S :
    (fun τ : ℍ ↦ θ₃ τ ^ 4) ∣[(2 : ℤ)] S = -fun τ : ℍ ↦ θ₃ τ ^ 4 := by
  ext τ
  simp only [SL_slash_apply, jacobiTheta_S_smul, denom_S, mul_pow, cpow_one_half_pow_four,
    Pi.neg_apply]
  field_simp [τ.ne_zero]

public theorem jacobiTheta₀₁_pow_four_slash_S :
    (fun τ : ℍ ↦ θ₄ τ ^ 4) ∣[(2 : ℤ)] S = -fun τ : ℍ ↦ θ₂ τ ^ 4 := by
  ext τ
  simp only [SL_slash_apply, jacobiTheta₀₁_S_smul, denom_S, mul_pow, cpow_one_half_pow_four,
    Pi.neg_apply]
  field_simp [τ.ne_zero]

/-!
## Jacobi's identity
-/

/-- The auxiliary function `θ₂ ^ 4 + θ₄ ^ 4 - θ₃ ^ 4` on `ℍ`, which we show to be zero. -/
noncomputable def g : ℍ → ℂ := (θ₂ · ^ 4 : ℍ → ℂ) + (θ₄ · ^ 4 : ℍ → ℂ) - (θ₃ · ^ 4 : ℍ → ℂ)

lemma g_apply : g = (θ₂ · ^ 4 : ℍ → ℂ) + (θ₄ · ^ 4 : ℍ → ℂ) - (θ₃ · ^ 4 : ℍ → ℂ) := rfl

lemma g_slash_S : g ∣[(2 : ℤ)] S = -g := by
  simp only [g_apply, SlashAction.sub_slash, SlashAction.add_slash, jacobiTheta₁₀_pow_four_slash_S,
    jacobiTheta_pow_four_slash_S, jacobiTheta₀₁_pow_four_slash_S]
  abel

lemma g_slash_T : g ∣[(2 : ℤ)] T = -g := by
  simp only [g, SlashAction.sub_slash, SlashAction.add_slash, jacobiTheta₁₀_pow_four_slash_T,
    jacobiTheta_pow_four_slash_T, jacobiTheta₀₁_pow_four_slash_T]
  abel

lemma g_sq_slash {γ : SL(2, ℤ)} (h : g ∣[(2 : ℤ)] γ = -g) :
    (g ^ 2) ∣[(4 : ℤ)] γ = g ^ 2 := by
  rw [(by norm_num : (4 : ℤ) = (2 : ℕ) * 2), pow_slash_SL2, h, neg_sq]

/-- `g ^ 2` as a cusp form of weight `4` and level one. -/
noncomputable def cuspForm : CuspForm 𝒮ℒ 4 where
  toFun := g ^ 2
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (g_sq_slash g_slash_S) (g_sq_slash g_slash_T) A
  holo' :=
    (((mdifferentiable_jacobiTheta₁₀.pow 4).add (mdifferentiable_jacobiTheta₀₁.pow 4)).sub
      (mdifferentiable_jacobiTheta.pow 4)).pow 2
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z (g_sq_slash g_slash_S) (g_sq_slash g_slash_T)]
    have := ((((tendsto_jacobiTheta₁₀_at_im_infty.comp tendsto_coe_atImInfty).pow 4).add
      ((tendsto_jacobiTheta₀₁_at_im_infty.comp tendsto_coe_atImInfty).pow 4)).sub
      ((tendsto_jacobiTheta_at_im_infty.comp tendsto_coe_atImInfty).pow 4)).pow 2
    rwa [(by norm_num : ((0 : ℂ) ^ 4 + 1 ^ 4 - 1 ^ 4) ^ 2 = 0)] at this

/-- **Jacobi's identity** `θ₂ ^ 4 + θ₄ ^ 4 = θ₃ ^ 4`. -/
public theorem jacobiTheta₁₀_pow_four_add_jacobiTheta₀₁_pow_four (τ : ℂ) :
    θ₂ τ ^ 4 + θ₄ τ ^ 4 = θ₃ τ ^ 4 := by
  rcases lt_or_ge 0 τ.im with hτ | hτ
  · have h : g ^ 2 = 0 := congr_arg (⇑) <| rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) cuspForm
    simpa [g, sub_eq_zero] using congr_fun h (.mk τ hτ)
  · simp [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₀₁_eq_jacobiTheta₂,
      jacobiTheta₁₀_eq_jacobiTheta₂, jacobiTheta₂_undef _ hτ]

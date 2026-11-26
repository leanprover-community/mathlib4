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

public section

open Complex ModularGroup ModularForm SlashInvariantForm Filter
open UpperHalfPlane hiding I

open scoped Real Topology Manifold MatrixGroups JacobiTheta

namespace JacobiTheta

/-!
## The fourth powers `H₂`, `H₃` and `H₄`
-/

/-- `H₂ = θ₂ ^ 4`, as a function on `ℍ`. -/
@[expose] noncomputable def H₂ (τ : ℍ) : ℂ := θ₂ τ ^ 4

/-- `H₃ = θ₃ ^ 4`, as a function on `ℍ`. -/
@[expose] noncomputable def H₃ (τ : ℍ) : ℂ := θ₃ τ ^ 4

/-- `H₄ = θ₄ ^ 4`, as a function on `ℍ`. -/
@[expose] noncomputable def H₄ (τ : ℍ) : ℂ := θ₄ τ ^ 4

@[simp] lemma H₂_apply (τ : ℍ) : H₂ τ = θ₂ τ ^ 4 := rfl

@[simp] lemma H₃_apply (τ : ℍ) : H₃ τ = θ₃ τ ^ 4 := rfl

@[simp] lemma H₄_apply (τ : ℍ) : H₄ τ = θ₄ τ ^ 4 := rfl

lemma mdifferentiable_H₂ : MDiff H₂ := mdifferentiable_jacobiTheta₁₀.pow 4

lemma mdifferentiable_H₃ : MDiff H₃ := mdifferentiable_jacobiTheta.pow 4

lemma mdifferentiable_H₄ : MDiff H₄ := mdifferentiable_jacobiTheta₀₁.pow 4

lemma tendsto_H₂_atImInfty : Tendsto H₂ atImInfty (𝓝 0) := by
  rw [← zero_pow four_ne_zero]
  exact (tendsto_jacobiTheta₁₀_at_im_infty.comp tendsto_coe_atImInfty).pow 4

lemma tendsto_H₃_atImInfty : Tendsto H₃ atImInfty (𝓝 1) := by
  rw [← one_pow 4]
  exact (tendsto_jacobiTheta_at_im_infty.comp tendsto_coe_atImInfty).pow 4

lemma tendsto_H₄_atImInfty : Tendsto H₄ atImInfty (𝓝 1) := by
  rw [← one_pow 4]
  exact (tendsto_jacobiTheta₀₁_at_im_infty.comp tendsto_coe_atImInfty).pow 4

/-!
## The action of `S` and `T`
-/

private lemma cpow_one_half_pow_four (z : ℂ) : ((-I * z) ^ (1 / 2 : ℂ)) ^ 4 = -z ^ 2 := by
  rw [← cpow_mul_nat, (by norm_num : (1 / 2 : ℂ) * (4 : ℕ) = 2), cpow_ofNat, mul_pow, neg_sq,
    I_sq, neg_one_mul]

theorem H₂_slash_T : H₂ ∣[(2 : ℤ)] T = -H₂ := by
  have h : cexp (π * I / 4) ^ 4 = -1 := by
    rw [← Complex.exp_natCast_mul, ← exp_pi_mul_I]
    ring_nf
  ext τ
  rw [SL_slash_apply, denom, modular_T_smul]
  simp [jacobiTheta₁₀_one_add, mul_pow, h]

theorem H₃_slash_T : H₃ ∣[(2 : ℤ)] T = H₄ := by
  ext τ
  rw [SL_slash_apply, denom, modular_T_smul]
  simp [jacobiTheta_one_add]

theorem H₄_slash_T : H₄ ∣[(2 : ℤ)] T = H₃ := by
  ext τ
  rw [SL_slash_apply, denom, modular_T_smul]
  simp [jacobiTheta₀₁_one_add]

theorem H₂_slash_S : H₂ ∣[(2 : ℤ)] S = -H₄ := by
  ext τ
  simp only [SL_slash_apply, H₂_apply, H₄_apply, jacobiTheta₁₀_S_smul, denom_S, mul_pow,
    cpow_one_half_pow_four, Pi.neg_apply]
  field_simp [τ.ne_zero]

theorem H₃_slash_S : H₃ ∣[(2 : ℤ)] S = -H₃ := by
  ext τ
  simp only [SL_slash_apply, H₃_apply, jacobiTheta_S_smul, denom_S, mul_pow,
    cpow_one_half_pow_four, Pi.neg_apply]
  field_simp [τ.ne_zero]

theorem H₄_slash_S : H₄ ∣[(2 : ℤ)] S = -H₂ := by
  ext τ
  simp only [SL_slash_apply, H₂_apply, H₄_apply, jacobiTheta₀₁_S_smul, denom_S, mul_pow,
    cpow_one_half_pow_four, Pi.neg_apply]
  field_simp [τ.ne_zero]

/-!
## Jacobi's identity
-/

/-- The auxiliary function `H₂ + H₄ - H₃`, which we show to be zero. -/
private noncomputable def g : ℍ → ℂ := H₂ + H₄ - H₃

private lemma g_slash_S : g ∣[(2 : ℤ)] S = -g := by
  simp only [g, SlashAction.sub_slash, SlashAction.add_slash, H₂_slash_S, H₃_slash_S, H₄_slash_S]
  abel

private lemma g_slash_T : g ∣[(2 : ℤ)] T = -g := by
  simp only [g, SlashAction.sub_slash, SlashAction.add_slash, H₂_slash_T, H₃_slash_T, H₄_slash_T]
  abel

private lemma g_sq_slash {γ : SL(2, ℤ)} (h : g ∣[(2 : ℤ)] γ = -g) :
    (g ^ 2) ∣[(4 : ℤ)] γ = g ^ 2 := by
  rw [(by norm_num : (4 : ℤ) = (2 : ℕ) * 2), pow_slash_SL2, h, neg_sq]

/-- `g ^ 2` as a cusp form of weight `4` and level one. -/
private noncomputable def cuspForm : CuspForm 𝒮ℒ 4 where
  toFun := g ^ 2
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (g_sq_slash g_slash_S) (g_sq_slash g_slash_T) A
  holo' := ((mdifferentiable_H₂.add mdifferentiable_H₄).sub mdifferentiable_H₃).pow 2
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z (g_sq_slash g_slash_S) (g_sq_slash g_slash_T)]
    have := ((tendsto_H₂_atImInfty.add tendsto_H₄_atImInfty).sub tendsto_H₃_atImInfty).pow 2
    rwa [(by norm_num : ((0 : ℂ) + 1 - 1) ^ 2 = 0)] at this

/-- **Jacobi's identity** `H₂ + H₄ = H₃`, i.e. `θ₂ ^ 4 + θ₄ ^ 4 = θ₃ ^ 4` on `ℍ`. -/
theorem H₂_add_H₄ : H₂ + H₄ = H₃ := by
  have h : (H₂ + H₄ - H₃) ^ 2 = 0 := congr_arg (⇑) <| rank_zero_iff_forall_zero.mp
    (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) cuspForm
  ext τ
  simpa [sub_eq_zero] using congr_fun h τ

end JacobiTheta

open JacobiTheta in
/-- **Jacobi's identity** `θ₂ ^ 4 + θ₄ ^ 4 = θ₃ ^ 4`. -/
theorem jacobiTheta₁₀_pow_four_add_jacobiTheta₀₁_pow_four (τ : ℂ) :
    θ₂ τ ^ 4 + θ₄ τ ^ 4 = θ₃ τ ^ 4 := by
  rcases lt_or_ge 0 τ.im with hτ | hτ
  · simpa using congr_fun H₂_add_H₄ (.mk τ hτ)
  · simp [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₀₁_eq_jacobiTheta₂,
      jacobiTheta₁₀_eq_jacobiTheta₂, jacobiTheta₂_undef _ hτ]

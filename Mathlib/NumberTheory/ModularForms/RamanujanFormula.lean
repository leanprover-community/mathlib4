/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.NumberTheory.ModularForms.Derivative

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Ramanujan's formulas for derivatives of Eisenstein series

We prove Ramanujan's formulas for derivatives of the normalised Eisenstein series `E₂`, `E₄`,
`E₆`, in terms of the Serre derivative `∂ₖ = D - (k / 12) E₂` and the normalized derivative
`D = (2πi)⁻¹ d/dz`:

- `Derivative.serreDerivative_E₂` : `∂₁ E₂ = -E₄ / 12`
- `Derivative.serreDerivative_E₄` : `∂₄ E₄ = -E₆ / 3`
- `Derivative.serreDerivative_E₆` : `∂₆ E₆ = -E₄² / 2`
- `Derivative.normalizedDerivOfComplex_E₂` : `D E₂ = (E₂² - E₄) / 12`
- `Derivative.normalizedDerivOfComplex_E₄` : `D E₄ = (E₂ E₄ - E₆) / 3`
- `Derivative.normalizedDerivOfComplex_E₆` : `D E₆ = (E₂ E₆ - E₄²) / 2`

## Proof Strategy

Proof uses dimension formula of modular forms of level 1, and the (Serre derivative) identities
are obtained by showing that the limit of both sides at `i∞` agree.
-/

open UpperHalfPlane hiding I
open Real Complex Filter EisensteinSeries ModularForm
open scoped Manifold MatrixGroups Topology

namespace Derivative

public noncomputable section

/-- The dimension argument: let `F` be a weight-`k'` modular form whose underlying function is
the Serre derivative `∂_κ f` of a holomorphic `f` with limit `l` at `i∞`. If the space of
weight-`k'` forms has rank one with a generator `g` tending to `1` at `i∞`, then
`∂_κ f = -(κ / 12) l • g`. -/
private lemma serreDerivative_eq_smul {k' : ℤ} {k l L : ℂ} {g F : ModularForm 𝒮ℒ k'}
    {f : ℍ → ℂ} (hF : F = serreDerivative k f)
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ k') = 1) (hf : MDiff f)
    (hl : Tendsto f atImInfty (𝓝 l)) (hg1 : Tendsto g atImInfty (𝓝 1))
    (hL : L = -(k * 12⁻¹ * l)) :
    serreDerivative k f = L • g := by
  have hg : g ≠ 0 := fun h ↦ one_ne_zero (tendsto_nhds_unique (h ▸ hg1) tendsto_const_nhds)
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' g hg).mp (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) F
  have hfg : serreDerivative k f = c • g := hF ▸ congrArg DFunLike.coe hc.symm
  have hlim : Tendsto (c • ⇑g) atImInfty (𝓝 (-(k * 12⁻¹ * l))) := hfg ▸ by
    simpa using (isZeroAtImInfty_normalizedDerivOfComplex hf (hl.isBigO_one ℝ)).sub
      ((tendsto_E2_atImInfty.const_mul (k * 12⁻¹)).mul hl)
  rw [hfg, hL, ← tendsto_nhds_unique (hg1.const_mul c) hlim, mul_one]

/-- **Ramanujan's formula for `E₄`**: `∂₄ E₄ = -E₆ / 3`. -/
theorem serreDerivative_E₄ : serreDerivative 4 E₄ = (-3⁻¹ : ℂ) • E₆ :=
  serreDerivative_eq_smul (F := serreDerivativeMF 4 E₄) rfl levelOne_weight_six_rank_one
    E₄.holo' tendsto_E_atImInfty tendsto_E_atImInfty (by norm_num)

/-- **Ramanujan's formula for `E₆`**: `∂₆ E₆ = -E₄² / 2`. -/
theorem serreDerivative_E₆ : serreDerivative 6 E₆ = (-2⁻¹ : ℂ) • E₄ ^ 2 :=
  have hlim : Tendsto (fun z ↦ E₄ z ^ 2) atImInfty (𝓝 1) := by
    simpa using (tendsto_E_atImInfty).pow 2
  coe_pow E₄ 2 ▸ serreDerivative_eq_smul (F := serreDerivativeMF 6 E₆) (g := E₄.pow 2) rfl
    (by simpa [Nat.ModEq] using dimension_level_one 8 ⟨4, rfl⟩) E₆.holo'
    tendsto_E_atImInfty hlim (by norm_num)

/-- The normalized derivative of the modular defect `D2 γ` is `-(γ₁₀)² / denom γ ²`. -/
lemma normalizedDerivOfComplex_D2 (γ : SL(2, ℤ)) :
    D (D2 γ) = fun z : ℍ ↦ -(γ 1 0 : ℂ) ^ 2 / denom γ z ^ 2 := by
  ext z
  have hcomp : (D2 γ ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      fun w ↦ 2 * π * I * (γ 1 0 : ℂ) * denom γ w ^ (-1 : ℤ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp [EisensteinSeries.D2, ofComplex_apply_of_im_pos hw, div_eq_mul_inv]
  simp only [normalizedDerivOfComplex, (((hasDerivAt_denom_zpow γ (-1) z).const_mul
    (2 * π * I * (γ 1 0 : ℂ))).congr_of_eventuallyEq hcomp).deriv]
  push_cast [show ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) = (γ 1 0 : ℝ) by norm_cast]
  field_simp

/-- Although `E₂` is only quasi-modular, its weight-1 Serre derivative `∂₁ E₂ = D E₂ - E₂² / 12`
is invariant under the weight-4 slash action of `SL(2, ℤ)`. -/
private lemma serreDerivativeOne_E2_slash (γ : SL(2, ℤ)) :
    serreDerivative 1 E2 ∣[(4 : ℤ)] γ = serreDerivative 1 E2 := by
  have hD2 : MDiff (D2 γ) := mdifferentiable_const.div (mdifferentiable_denom _) (denom_ne_zero _)
  have hD := normalizedDerivOfComplex_SL_slash (k := 2) E2_mdifferentiable (γ := γ)
  rw [E2_slash_action,
    normalizedDerivOfComplex_sub _ _ E2_mdifferentiable (hD2.const_smul _),
    normalizedDerivOfComplex_smul _ _ hD2] at hD
  have heq : serreDerivative 1 E2 = D E2 - (12⁻¹ : ℂ) • E2 ^ 2 := by
    ext z
    simp [pow_two, mul_assoc]
  rw [heq, SlashAction.sub_slash, SL_smul_slash, show (4 : ℤ) = (2 : ℕ) * 2 from rfl,
    pow_slash_SL2, E2_slash_action]
  ext z
  have hz := congrFun hD z
  simp [normalizedDerivOfComplex_D2, EisensteinSeries.D2, riemannZeta_two] at hz ⊢
  field_simp at hz ⊢
  linear_combination -6 * hz + 36 * (γ 1 0 : ℂ) ^ 2 * I_sq

/-- The weight-1 Serre derivative of `E₂`, packaged as a modular form of weight `4`. -/
private def serreDerivativeOneE2 : ModularForm 𝒮ℒ 4 where
  toFun := serreDerivative 1 E2
  slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ serreDerivativeOne_E2_slash γ
  holo' := serreDerivative_mdifferentiable 1 E2_mdifferentiable
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (serreDerivativeOne_E2_slash γ).symm ▸
      isBoundedAtImInfty_serreDerivative 1 E2_mdifferentiable isBoundedAtImInfty_E2

/-- **Ramanujan's formula for `E₂`**: `∂₁ E₂ = -E₄ / 12`. -/
theorem serreDerivative_E₂ : serreDerivative 1 E2 = (-12⁻¹ : ℂ) • E₄ :=
  serreDerivative_eq_smul (F := serreDerivativeOneE2) rfl levelOne_weight_four_rank_one
    E2_mdifferentiable tendsto_E2_atImInfty tendsto_E_atImInfty (by norm_num)

/-! ### Ramanujan's formulas in terms of `D` -/

/-- **Ramanujan's formula for `E₂`**: `D E₂ = (E₂² - E₄) / 12`. -/
theorem normalizedDerivOfComplex_E₂ : D E2 = (12⁻¹ : ℂ) • (E2 ^ 2 - E₄) := by
  linear_combination (norm := (funext z; simp; ring1)) serreDerivative_E₂

/-- **Ramanujan's formula for `E₄`**: `D E₄ = (E₂ E₄ - E₆) / 3`. -/
theorem normalizedDerivOfComplex_E₄ : D E₄ = (3⁻¹ : ℂ) • (E2 * E₄ - E₆) := by
  linear_combination (norm := (funext z; simp; ring1)) serreDerivative_E₄

/-- **Ramanujan's formula for `E₆`**: `D E₆ = (E₂ E₆ - E₄²) / 2`. -/
theorem normalizedDerivOfComplex_E₆ : D E₆ = (2⁻¹ : ℂ) • (E2 * E₆ - E₄ ^ 2) := by
  linear_combination (norm := (funext z; simp; ring1)) serreDerivative_E₆

end

end Derivative

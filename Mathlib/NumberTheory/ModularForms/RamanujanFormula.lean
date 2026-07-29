/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

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

Each Serre derivative is a modular form in a one-dimensional space, so it is a scalar multiple of
the generator, and the scalar is determined by the limit at `i∞`. Since `E₂` is only
quasi-modular, we prove directly that `∂₁ E₂` is modular of weight `4`
(`Derivative.serreDerivativeOneE2`).
-/

open UpperHalfPlane hiding I
open Real Complex Filter EisensteinSeries ModularForm
open scoped Manifold MatrixGroups ModularForm Topology

namespace Derivative

@[expose] public noncomputable section

/-- The dimension argument: let `F` be a weight-`k'` modular form whose underlying function is
the Serre derivative `∂_κ f` of a bounded holomorphic `f` with limit `l` at `i∞`. If the space
of weight-`k'` forms has rank one with a generator `g` tending to `1` at `i∞`, then
`∂_κ f = -(κ / 12) l • g`. -/
private lemma serreDerivative_eq_smul {k' : ℤ} {κ l L : ℂ} {g F : ModularForm 𝒮ℒ k'}
    {f g' : ℍ → ℂ} (hF : ⇑F = serreDerivative κ f)
    (hrank : Module.rank ℂ (ModularForm 𝒮ℒ k') = 1) (hg : g ≠ 0) (hG : ⇑g = g') (hf : MDiff f)
    (hb : IsBoundedAtImInfty f) (hl : Tendsto f atImInfty (𝓝 l))
    (hg1 : Tendsto g' atImInfty (𝓝 1)) (hL : L = -(κ * 12⁻¹ * l)) :
    serreDerivative κ f = L • g' := by
  subst hL
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' g hg).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) F
  have hfg : serreDerivative κ f = c • g' := hG ▸ hF ▸ congrArg DFunLike.coe hc.symm
  have hlim : Tendsto (c • g') atImInfty (𝓝 (-(κ * 12⁻¹ * l))) := hfg ▸ by
    simpa using (normalizedDerivOfComplex_isZeroAtImInfty hf hb).sub
      ((tendsto_E2_atImInfty.const_mul (κ * 12⁻¹)).mul hl)
  rw [hfg, ← tendsto_nhds_unique (hg1.const_mul c) hlim, mul_one]

/-- **Ramanujan's formula for `E₄`**: `∂₄ E₄ = -E₆ / 3`. -/
theorem serreDerivative_E₄ : serreDerivative 4 E₄ = (-3⁻¹ : ℂ) • E₆ :=
  serreDerivative_eq_smul (F := mcast (show (4 : ℤ) + 2 = 6 by norm_num) (serreDerivativeMF 4 E₄))
    (by rw [ModularForm.coe_mcast, coe_serreDerivativeMF, Int.cast_ofNat])
    levelOne_weight_six_rank_one (E_ne_zero (by norm_num) ⟨3, rfl⟩) rfl E₄.holo'
    (ModularFormClass.bdd_at_infty E₄) tendsto_E₄_atImInfty tendsto_E₆_atImInfty (by norm_num)

/-- **Ramanujan's formula for `E₆`**: `∂₆ E₆ = -E₄² / 2`. -/
theorem serreDerivative_E₆ : serreDerivative 6 E₆ = (-2⁻¹ : ℂ) • E₄ ^ 2 :=
  serreDerivative_eq_smul (F := mcast (show (6 : ℤ) + 2 = 8 by norm_num) (serreDerivativeMF 6 E₆))
    (g := mcast (by norm_num) (E₄.pow 2))
    (by rw [ModularForm.coe_mcast, coe_serreDerivativeMF, Int.cast_ofNat])
    (by simpa [Nat.ModEq] using dimension_level_one 8 ⟨4, rfl⟩)
    (DFunLike.ne_iff.mpr <| (DFunLike.ne_iff.mp <| E_ne_zero (by norm_num) ⟨2, rfl⟩).imp fun z hz ↦
      by simpa only [ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply,
        ModularForm.zero_apply] using pow_ne_zero 2 hz)
    (by rw [ModularForm.coe_mcast, ModularForm.coe_pow]) E₆.holo'
    (ModularFormClass.bdd_at_infty E₆) tendsto_E₆_atImInfty
    ((one_pow 2 : (1 : ℂ) ^ 2 = 1) ▸ tendsto_E₄_atImInfty.pow 2) (by norm_num)

/-- The normalized derivative of the modular defect `D2 γ` is `-(γ₁₀)² / denom γ ²`. -/
lemma normalizedDerivOfComplex_D2 (γ : SL(2, ℤ)) :
    D (D2 γ) = fun z : ℍ ↦ -(γ 1 0 : ℂ) ^ 2 / denom γ z ^ 2 := by
  ext z
  have hcomp : ((D2 γ) ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)]
      fun w ↦ 2 * π * I * (γ 1 0 : ℂ) * denom (γ : GL (Fin 2) ℝ) w ^ (-1 : ℤ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp [EisensteinSeries.D2, ofComplex_apply_of_im_pos hw, div_eq_mul_inv]
  simp only [normalizedDerivOfComplex, (((hasDerivAt_denom_zpow (γ : GL (Fin 2) ℝ) (-1) z).const_mul
    (2 * π * I * (γ 1 0 : ℂ))).congr_of_eventuallyEq hcomp).deriv]
  push_cast [show ((γ : GL (Fin 2) ℝ) 1 0 : ℝ) = (γ 1 0 : ℝ) by norm_cast]
  field_simp

/-- Although `E₂` is only quasi-modular, its weight-1 Serre derivative `∂₁ E₂ = D E₂ - E₂² / 12`
is invariant under the weight-4 slash action of `SL(2, ℤ)`. -/
lemma serreDerivativeOne_E2_slash (γ : SL(2, ℤ)) :
    serreDerivative 1 E2 ∣[(4 : ℤ)] γ = serreDerivative 1 E2 := by
  have hD2 : MDiff (D2 γ) :=
    mdifferentiable_const.div (mdifferentiable_denom _) fun w ↦ denom_ne_zero _ _
  have hDslash : D (E2 ∣[(2 : ℤ)] γ) = D E2 - (1 / (2 * riemannZeta 2)) • D (D2 γ) := by
    rw [E2_slash_action, normalizedDerivOfComplex_sub _ _ E2_mdifferentiable (hD2.const_smul _),
      normalizedDerivOfComplex_smul _ _ hD2]
  ext z
  have hLHS : (serreDerivative 1 E2 ∣[(4 : ℤ)] γ) z =
      (D E2 ∣[(4 : ℤ)] γ) z - 12⁻¹ * ((E2 ∣[(2 : ℤ)] γ) z * (E2 ∣[(2 : ℤ)] γ) z) := by
    grind [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply,
      congrFun (ModularForm.mul_slash_SL2 2 2 γ E2 E2) z]
  have hDE2 : (D E2 ∣[(4 : ℤ)] γ) z = D E2 z - 1 / (2 * riemannZeta 2) *
      (-(γ 1 0 : ℂ) ^ 2 / denom γ z ^ 2) +
      2 * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (E2 ∣[(2 : ℤ)] γ) z := by
    have hDz := congrFun (normalizedDerivOfComplex_SL_slash (k := 2) (γ := γ) E2_mdifferentiable) z
    have hDslashz := congrFun hDslash z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, show (2 : ℤ) + 2 = 4 by norm_num,
      Int.cast_ofNat, normalizedDerivOfComplex_D2] at hDz hDslashz
    linear_combination hDslashz - hDz
  rw [hLHS, serreDerivative_apply, hDE2, congrFun (E2_slash_action γ) z]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, EisensteinSeries.D2, riemannZeta_two]
  field_simp [denom_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  linear_combination (24 * (γ 1 0 : ℂ) * π * denom γ z * E2 z - 72 * (γ 1 0 : ℂ) ^ 2 * I) * I_sq

/-- The weight-1 Serre derivative of `E₂`, packaged as a modular form of weight `4`. -/
def serreDerivativeOneE2 : ModularForm 𝒮ℒ 4 where
  toSlashInvariantForm :=
    { toFun := serreDerivative 1 E2
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ serreDerivativeOne_E2_slash γ }
  holo' := serreDerivative_mdifferentiable 1 E2_mdifferentiable
  bdd_at_cusps' {_} hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
    (serreDerivativeOne_E2_slash γ).symm ▸
      serreDerivative_isBoundedAtImInfty 1 E2_mdifferentiable isBoundedAtImInfty_E2

/-- **Ramanujan's formula for `E₂`**: `∂₁ E₂ = -E₄ / 12`. -/
theorem serreDerivative_E₂ : serreDerivative 1 E2 = (-12⁻¹ : ℂ) • E₄ :=
  serreDerivative_eq_smul (F := serreDerivativeOneE2) rfl levelOne_weight_four_rank_one
    (E_ne_zero (by norm_num) ⟨2, rfl⟩) rfl E2_mdifferentiable isBoundedAtImInfty_E2
    tendsto_E2_atImInfty tendsto_E₄_atImInfty (by norm_num)

/-! ### Ramanujan's formulas in terms of `D` -/

/-- **Ramanujan's formula for `E₂`**: `D E₂ = (E₂² - E₄) / 12`. -/
theorem normalizedDerivOfComplex_E₂ : D E2 = (12⁻¹ : ℂ) • (E2 ^ 2 - E₄) := by
  funext z
  linear_combination (norm := (simp only [serreDerivative_apply, Pi.smul_apply, Pi.sub_apply,
    Pi.pow_apply, smul_eq_mul]; ring1)) congrFun serreDerivative_E₂ z

/-- **Ramanujan's formula for `E₄`**: `D E₄ = (E₂ E₄ - E₆) / 3`. -/
theorem normalizedDerivOfComplex_E₄ : D E₄ = (3⁻¹ : ℂ) • (E2 * E₄ - E₆) := by
  funext z
  linear_combination (norm := (simp only [serreDerivative_apply, Pi.smul_apply, Pi.sub_apply,
    Pi.mul_apply, smul_eq_mul]; ring1)) congrFun serreDerivative_E₄ z

/-- **Ramanujan's formula for `E₆`**: `D E₆ = (E₂ E₆ - E₄²) / 2`. -/
theorem normalizedDerivOfComplex_E₆ : D E₆ = (2⁻¹ : ℂ) • (E2 * E₆ - E₄ ^ 2) := by
  funext z
  linear_combination (norm := (simp only [serreDerivative_apply, Pi.smul_apply, Pi.sub_apply,
    Pi.mul_apply, Pi.pow_apply, smul_eq_mul]; ring1)) congrFun serreDerivative_E₆ z

end

end Derivative

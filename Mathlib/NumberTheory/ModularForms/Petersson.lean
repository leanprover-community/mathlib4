/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ModularForms.Basic

/-!
# The Petersson scalar product

For `f, f'` functions `ℍ → ℂ`, we define `petersson k f f'` to be the function
`τ ↦ conj (f τ) * f' τ * τ.im ^ k`.

We show this function is (weight 0) invariant under `Γ` if `f, f'` are (weight `k`) invariant under
`Γ`.
-/


open UpperHalfPlane

open scoped MatrixGroups ComplexConjugate ModularForm

namespace UpperHalfPlane

/-- The integrand in the Petersson scalar product of two modular forms. -/
noncomputable def petersson (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :=
  conj (f τ) * f' τ * τ.im ^ k

lemma petersson_continuous (k : ℤ) {f f' : ℍ → ℂ} (hf : Continuous f) (hf' : Continuous f') :
    Continuous (petersson k f f') := by
  apply ((Complex.continuous_conj.comp hf).mul hf').mul
  apply (Complex.continuous_ofReal.comp continuous_im).zpow₀
  exact fun τ ↦ .inl <| Complex.ofReal_ne_zero.mpr τ.im_ne_zero

lemma petersson_slash (k : ℤ) (f f' : ℍ → ℂ) (g : GL (Fin 2) ℝ) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ =
      |g.val.det| ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by
  set D := g.val.det
  have hD : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr <| g.det_ne_zero
  set j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = D ^ (2 * k - 2) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp [Complex.normSq_eq_conj_mul_self, (by ring : 2 * k - 2 = (k - 1) + (k - 1)),
      zpow_add₀ hD, mul_zpow, ModularForm.slash_def, petersson]
    ring
  _ = |D| ^ (2 * k - 2) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp only [← Complex.ofReal_zpow, (show Even (2 * k - 2) by aesop).zpow_abs]
  _ = |D| ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (|D| * τ.im / j.normSq) ^ k) := by
    rw [div_zpow, mul_zpow, zpow_neg, div_eq_mul_inv, (by ring : 2 * k - 2 = k + (k - 2)),
      zpow_add₀ (by aesop)]
    ring
  _ = |D| ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq, Complex.ofReal_div, Complex.ofReal_mul,
      Matrix.GeneralLinearGroup.val_det_apply]
  _ = |D| ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by simp [petersson, σ_conj]

lemma petersson_slash_SL (k : ℤ) (f f' : ℍ → ℂ) (g : SL(2, ℤ)) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ = petersson k f f' (g • τ) := by
  -- need to disable two simp lemmas as they work against `Matrix.SpecialLinearGroup.det_coe`
  simp [σ, ModularForm.SL_slash, petersson_slash,
    -Matrix.SpecialLinearGroup.map_apply_coe, -Matrix.SpecialLinearGroup.coe_matrix_coe]

end UpperHalfPlane

section

variable {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]

lemma SlashInvariantFormClass.petersson_smul {k : ℤ} {Γ : Subgroup SL(2, ℤ)}
    [SlashInvariantFormClass F Γ k] {f : F} [SlashInvariantFormClass F' Γ k] {f' : F'}
    {g : SL(2, ℤ)} (hg : g ∈ Γ) {τ : ℍ} :
    petersson k f f' (g • τ) = petersson k f f' τ := by
  simpa only [SlashInvariantFormClass.slash_action_eq _ _ hg]
    using (petersson_slash_SL k f f' g τ).symm

lemma ModularFormClass.petersson_continuous (k : ℤ) (Γ : Subgroup SL(2, ℤ))
    [ModularFormClass F Γ k] [ModularFormClass F' Γ k] (f : F) (f' : F') :
    Continuous (petersson k f f') :=
  UpperHalfPlane.petersson_continuous k
    (ModularFormClass.holo f).continuous (ModularFormClass.holo f').continuous

end

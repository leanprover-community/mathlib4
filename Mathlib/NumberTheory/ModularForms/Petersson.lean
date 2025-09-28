/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

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

@[fun_prop]
lemma petersson_continuous (k : ℤ) {f f' : ℍ → ℂ} (hf : Continuous f) (hf' : Continuous f') :
    Continuous (petersson k f f') := by
  unfold petersson
  fun_prop (disch := simp [im_ne_zero _])

lemma petersson_slash (k : ℤ) (f f' : ℍ → ℂ) (g : GL (Fin 2) ℝ) (τ : ℍ) :
    petersson k (f ∣[k] g) (f' ∣[k] g) τ =
      |g.det.val| ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by
  set D := |g.det.val|
  have hD : (D : ℂ) ≠ 0 := mod_cast abs_ne_zero.mpr g.det_ne_zero
  set j := denom g τ
  calc petersson k (f ∣[k] g) (f' ∣[k] g) τ
  _ = D ^ (k - 2 + k) * conj (σ g (f (g • τ))) * σ g (f' (g • τ))
      * (τ.im ^ k * j.normSq ^ (-k)) := by
    simp [Complex.normSq_eq_conj_mul_self, (by abel : k - 2 + k = (k - 1) + (k - 1)), petersson,
      zpow_add₀ hD, mul_zpow, ModularForm.slash_def, -Matrix.GeneralLinearGroup.val_det_apply]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (D * τ.im / j.normSq) ^ k) := by
    rw [div_zpow, mul_zpow, zpow_neg, div_eq_mul_inv, zpow_add₀ hD]
    ring
  _ = D ^ (k - 2) * (conj (σ g (f (g • τ))) * σ g (f' (g • τ)) * (im (g • τ)) ^ k) := by
    rw [im_smul_eq_div_normSq, Complex.ofReal_div, Complex.ofReal_mul]
  _ = D ^ (k - 2) * σ g (petersson k f f' (g • τ)) := by simp [petersson, σ_conj]

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

end

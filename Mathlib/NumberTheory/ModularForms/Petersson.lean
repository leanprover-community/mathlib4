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
`Γ`, and it vanishes at infinity if `f, f'` are bounded at infinity and one of them vanishes.
-/


open Topology Filter UpperHalfPlane Asymptotics

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

/-- If `f, f'` are modular forms and `f` is zero at infinity, then `petersson k f f'` has
exponentially rapid decay at infinity. -/
lemma IsZeroAtImInfty.petersson_exp_decay_left
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] {f : F} (h_bd : IsZeroAtImInfty f)
    {F' : Type*} [FunLike F' ℍ ℂ] [ModularFormClass F' Γ k] (f' : F') :
    ∃ a > 0, petersson k f f' =O[atImInfty] fun τ ↦ Real.exp (-a * im τ) := by
  obtain ⟨b, hb, hbf⟩ := h_bd.exp_decay_atImInfty
  have hf' : IsBoundedAtImInfty f' := by simpa using ModularFormClass.bdd_at_infty f' 1
  obtain ⟨a, ha, ha'⟩ := exists_between hb
  use a, ha
  apply IsBigO.of_norm_left
  simp_rw [petersson, norm_mul, Complex.norm_conj, mul_comm ‖f _‖ ‖f' _‖, norm_zpow, mul_assoc,
      Complex.norm_real, Real.norm_of_nonneg (fun {τ : ℍ} ↦ τ.im_pos).le]
  conv_rhs => enter [τ]; rw [← one_mul (Real.exp _)]
  refine hf'.norm_left.mul ((hbf.norm_left.mul <| isBigO_refl _ _).trans ?_)
  refine IsBigO.comp_tendsto (f := fun t : ℝ ↦ Real.exp (-b * t) * t ^ k)
    (g := fun t : ℝ ↦ Real.exp (-a * t)) ?_ tendsto_comap
  refine (isLittleO_of_tendsto (fun _ h ↦ (Real.exp_ne_zero _ h).elim) ?_).isBigO
  simp_rw [← div_mul_eq_mul_div₀, ← Real.exp_sub, ← sub_mul, neg_sub_neg, ← neg_sub b a,
    mul_comm _ (_ ^ k), ← Real.rpow_intCast]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (sub_pos.mpr ha')

/-- If `f, f'` are modular forms and `f'` is zero at infinity, then `petersson k f f'` has
exponentially rapid decay at infinity. -/
lemma IsZeroAtImInfty.petersson_exp_decay_right
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F)
    {F' : Type*} [FunLike F' ℍ ℂ] [ModularFormClass F' Γ k] {f' : F'} (h_bd : IsZeroAtImInfty f') :
    ∃ a > 0, petersson k f f' =O[atImInfty] fun τ ↦ Real.exp (-a * im τ) := by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f
  use a, ha
  rw [← isBigO_norm_left] at ha' ⊢
  refine ha'.congr_left fun τ ↦ ?_
  simp only [petersson, norm_mul, Complex.norm_conj, mul_comm]

lemma IsZeroAtImInfty.petersson_isZeroAtImInfty_left
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] {f : F} (h_bd : IsZeroAtImInfty f)
    {F' : Type*} [FunLike F' ℍ ℂ] [ModularFormClass F' Γ k] (f' : F') :
    IsZeroAtImInfty (petersson k f f') := by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f'
  refine ha'.trans_tendsto <| (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

lemma IsZeroAtImInfty.petersson_isZeroAtImInfty_right
    (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F)
    {F' : Type*} [FunLike F' ℍ ℂ] [ModularFormClass F' Γ k] {f' : F'}
    (h_bd : IsZeroAtImInfty f') : IsZeroAtImInfty (petersson k f f') := by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_right k Γ f
  refine ha'.trans_tendsto <| (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

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

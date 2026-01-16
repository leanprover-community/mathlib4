/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The Petersson scalar product

For `f, f'` functions `ℍ → ℂ`, we define `petersson k f f'` to be the function
`τ ↦ conj (f τ) * f' τ * τ.im ^ k`.

We show this function is (weight 0) invariant under `Γ` if `f, f'` are (weight `k`) invariant under
`Γ`.
-/

@[expose] public section


open UpperHalfPlane Asymptotics Filter

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

lemma petersson_symm (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :
    petersson k f' f τ = conj (petersson k f f' τ) := by
  simp [petersson, mul_comm]

lemma petersson_norm_symm (k : ℤ) (f f' : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k f' f τ‖ = ‖petersson k f f' τ‖ := by
  simp [petersson_symm k f]

end UpperHalfPlane

section

variable {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]

lemma SlashInvariantFormClass.norm_petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.HasDetPlusMinusOne] [SlashInvariantFormClass F Γ k] {f : F}
    [SlashInvariantFormClass F' Γ k] {f' : F'} (hg : g ∈ Γ) :
    ‖petersson k f f' (g • τ)‖ = ‖petersson k f f' τ‖ := by
  conv_rhs => rw [← slash_action_eq f _ hg, ← slash_action_eq f' _ hg, petersson_slash,
    Subgroup.HasDetPlusMinusOne.abs_det hg, Complex.ofReal_one, one_zpow, one_mul, norm_σ]

lemma SlashInvariantFormClass.petersson_smul {k g τ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    [SlashInvariantFormClass F Γ k] {f : F} [SlashInvariantFormClass F' Γ k] {f' : F'}
    (hg : g ∈ Γ) : petersson k f f' (g • τ) = petersson k f f' τ := by
  simpa [SlashInvariantFormClass.slash_action_eq _ _ hg, Subgroup.HasDetOne.det_eq hg, σ]
    using (petersson_slash k f f' g τ).symm

namespace UpperHalfPlane.IsZeroAtImInfty

variable (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ))
    [Fact (IsCusp OnePoint.infty Γ)] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [ModularFormClass F Γ k] [ModularFormClass F' Γ k]

include Γ -- can't be inferred from statements

/-- If `f, f'` are modular forms and `f` is zero at infinity, then `petersson k f f'` has
exponentially rapid decay at infinity. -/
lemma petersson_exp_decay_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') :
    ∃ a > 0, petersson k f f' =O[atImInfty] fun τ ↦ Real.exp (-a * im τ) := by
  obtain ⟨b, hb, hbf⟩ := h_bd.exp_decay_atImInfty'
  obtain ⟨a, ha, ha'⟩ := exists_between hb
  use a, ha
  apply IsBigO.of_norm_left
  simp_rw [petersson, norm_mul, Complex.norm_conj, mul_comm ‖f _‖ ‖f' _‖, norm_zpow, mul_assoc,
      Complex.norm_real, Real.norm_of_nonneg (fun {τ : ℍ} ↦ τ.im_pos).le]
  conv_rhs => enter [τ]; rw [← one_mul (Real.exp _)]
  have hf' : IsBoundedAtImInfty f' := ModularFormClass.bdd_at_infty f'
  refine hf'.norm_left.mul ((hbf.norm_left.mul <| isBigO_refl _ _).trans ?_)
  refine IsBigO.comp_tendsto (f := fun t : ℝ ↦ Real.exp (-b * t) * t ^ k)
     (g := fun t : ℝ ↦ Real.exp (-a * t)) ?_ tendsto_comap
  simpa using (isLittleO_exp_mul_rpow_of_lt k (neg_lt_neg ha')).isBigO

/-- If `f, f'` are modular forms and `f'` is zero at infinity, then `petersson k f f'` has
exponentially rapid decay at infinity. -/
lemma petersson_exp_decay_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') :
    ∃ a > 0, petersson k f f' =O[atImInfty] fun τ ↦ Real.exp (-a * im τ) := by
  obtain ⟨a, ha, ha'⟩ := h_bd.petersson_exp_decay_left k Γ f
  exact ⟨a, ha, .of_norm_left <| ha'.norm_left.congr_left <| petersson_norm_symm k f f'⟩

omit Γ in
-- this lemma can't go in `UpperHalfPlane.FunctionsBoundedAtInfty` because it needs `Real.exp`
lemma of_exp_decay {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    (hf : ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
    IsZeroAtImInfty f := by
  obtain ⟨a, ha, ha'⟩ := hf
  refine ha'.trans_tendsto <| (Real.tendsto_exp_atBot.comp ?_).comp tendsto_comap
  exact tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha)

lemma petersson_isZeroAtImInfty_left {f : F} (h_bd : IsZeroAtImInfty f) (f' : F') :
    IsZeroAtImInfty (petersson k f f') :=
  of_exp_decay (h_bd.petersson_exp_decay_left k Γ f')

lemma petersson_isZeroAtImInfty_right (f : F) {f' : F'} (h_bd : IsZeroAtImInfty f') :
    IsZeroAtImInfty (petersson k f f') :=
  of_exp_decay (h_bd.petersson_exp_decay_right k Γ f)

end UpperHalfPlane.IsZeroAtImInfty

end

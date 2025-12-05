/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne

/-!
# Norm and trace maps

Given two subgroups `𝒢, ℋ` of `GL(2, ℝ)` with `𝒢.relindex ℋ ≠ 0` (i.e. `𝒢 ⊓ ℋ` has finite index
in `ℋ`), we define a trace map from `ModularForm (𝒢 ⊓ ℋ) k` to `ModularForm ℋ k`.
-/
@[expose] public noncomputable section

open UpperHalfPlane

open scoped ModularForm Topology Filter Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

instance : MulAction ℋ ℋ := Monoid.toMulAction ..
instance : MulAction ℋ 𝒬 := .quotient ..

namespace SlashInvariantForm

variable [SlashInvariantFormClass F 𝒢 k]

/-- For `f` invariant under `𝒢`, this is a function on `(ℋ ⧸ 𝒢 ⊓ ℋ) × ℍ → ℂ` which packages up the
translates of `f` by `ℋ`. -/
def quotientFunc (q : 𝒬) (τ : ℍ) : ℂ :=
  q.liftOn (fun g ↦ ((f : ℍ → ℂ) ∣[k] g.val⁻¹) τ) (fun h h' hhh' ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ g ∈ 𝒢, h' = h * g := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    simp [hj', SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f j⁻¹ (inv_mem hj)])

lemma quotientFunc_mk (h : ℋ) : quotientFunc f ⟦h⟧ = (f : ℍ → ℂ) ∣[k] h.val⁻¹ :=
  rfl

lemma quotientFunc_smul {h} (hh : h ∈ ℋ) (q : 𝒬) :
    quotientFunc f q ∣[k] h = quotientFunc f ((⟨h, hh⟩ : ℋ)⁻¹ • q) := by
  induction q using Quotient.inductionOn with | h r =>
  simp [quotientFunc_mk, SlashAction.slash_mul]

variable (ℋ)

/-- The trace of a slash-invariant form, as a slash-invariant form. -/
protected def trace [𝒢.IsFiniteRelIndex ℋ] : SlashInvariantForm ℋ k where
  toFun := let := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _

/-- The norm of a slash-invariant form, as a slash-invariant form. -/
protected def norm [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] :
    SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := let := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash Finset.univ_nonempty,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _

end SlashInvariantForm

open SlashInvariantForm

section ModularForm

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a modular form, as a modular form. -/
protected def ModularForm.trace [ModularFormClass F 𝒢 k] : ModularForm ℋ k where
  __ := SlashInvariantForm.trace ℋ f
  holo' := by
    simp only [SlashInvariantForm.trace, SlashInvariantForm.coe_mk]
    refine MDifferentiable.finset_sum fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h r =>
    simpa only [quotientFunc_mk, ← Function.comp_def (f := f ∣[k] r.val⁻¹),
      ← UpperHalfPlane.mdifferentiable_iff] using (ModularForm.translate f r.val⁻¹).holo'
  bdd_at_cusps' h γ := by
    rintro rfl
    simp_rw [SlashInvariantForm.trace, IsBoundedAtImInfty, Filter.BoundedAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    refine .sum fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h r =>
    obtain ⟨r, hr⟩ := r
    refine (ModularForm.translate f _).bdd_at_cusps' ?_ γ rfl
    simp only [inv_inv]
    apply h.of_relindex_ne_zero
    rw [← Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hr),
      Subgroup.relIndex_pointwise_smul]
    exact Subgroup.IsFiniteRelIndex.relIndex_ne_zero

/-- The trace of a cusp form, as a cusp form. -/
protected def CuspForm.trace [CuspFormClass F 𝒢 k] : CuspForm ℋ k where
  __ := ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.trace, SlashInvariantForm.trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    let := Fintype.ofFinite 𝒬
    rw [show (0 : ℂ) = ∑ c : ℋ ⧸ 𝒢.subgroupOf ℋ, 0 by simp]
    refine tendsto_finset_sum .univ fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h r =>
    obtain ⟨r, hr⟩ := r
    refine (CuspForm.translate f _).zero_at_cusps' ?_ γ rfl
    simp only [inv_inv]
    apply h.of_relindex_ne_zero
    rw [← ℋ.conjAct_pointwise_smul_eq_self (ℋ.le_normalizer hr), 𝒢.relIndex_pointwise_smul]
    exact Subgroup.IsFiniteRelIndex.relIndex_ne_zero

/-- The norm of a modular form, as a modular form. -/
def ModularForm.norm [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm ℋ (k * Nat.card 𝒬) where
  __ := SlashInvariantForm.norm ℋ f
  holo' := by
    simp only [SlashInvariantForm.norm, SlashInvariantForm.coe_mk]
    refine MDifferentiable.finset_prod fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h r =>
    simpa [quotientFunc_mk, ← Function.comp_def (f := f ∣[k] r.val⁻¹),
      ← UpperHalfPlane.mdifferentiable_iff] using (ModularForm.translate f r.val⁻¹).holo'
  bdd_at_cusps' h γ := by
    rintro rfl
    let := Fintype.ofFinite 𝒬
    simp_rw [SlashInvariantForm.norm, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    rw [Nat.card_eq_fintype_card, ModularForm.prod_fintype_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = (fun x ↦ ∏ (i : 𝒬), 1) by ext; simp, Finset.prod_fn]
    apply Asymptotics.IsBigO.finsetProd fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h r =>
    obtain ⟨r, hr⟩ := r
    refine (ModularForm.translate f _).bdd_at_cusps' ?_ γ rfl
    simp only [inv_inv]
    apply h.of_relindex_ne_zero
    rw [← Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hr),
      Subgroup.relIndex_pointwise_smul]
    exact Subgroup.IsFiniteRelIndex.relIndex_ne_zero

lemma ModularForm.norm_ne_zero [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
    (hf : (f : ℍ → ℂ) ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, ModularForm.norm ℋ f z ≠ 0 := by
  have (q : 𝒬) : ∀ᶠ z in 𝓝[≠] τ, quotientFunc f q z ≠ 0 := by
    induction q using Quotient.inductionOn with | h r =>
    simp only [quotientFunc_mk]
    contrapose! hf
    have := UpperHalfPlane.eq_zero_of_frequently
      (ModularForm.translate f r.val⁻¹).holo' (τ := τ) hf
    have : (f : ℍ → ℂ) ∣[k] r.val⁻¹ = 0 := this
    apply_fun (fun g ↦ g ∣[k] r.val) at this
    rwa [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] at this
  filter_upwards [Filter.eventually_all.mpr this] with z hz
  simp only [ModularForm.norm, SlashInvariantForm.norm, Finset.prod_fn, ← ModularForm.toFun_eq_coe]
  exact Finset.prod_ne_zero_iff.mpr fun q _ ↦ hz q

open scoped MatrixGroups

lemma ModularForm.isZero_of_neg_weight {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (hk : k < 0) (f : ModularForm Γ k) : f = 0 := by
  have : Γ.IsFiniteRelIndex 𝒮ℒ := by
    constructor
    rw [MonoidHom.range_eq_map, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (Subgroup.IsArithmetic.finiteIndex_comap Γ).index_ne_zero
  have : ModularForm.norm 𝒮ℒ f = 0 := by
    ext
    rw [@ModularFormClass.levelOne_neg_weight_eq_zero (f := ModularForm.norm 𝒮ℒ f) _ _ _]
    · tauto
    · rw [CongruenceSubgroup.Gamma_one_top, MonoidHom.range_eq_map]
      infer_instance
    · refine mul_neg_of_neg_of_pos hk ?_
      norm_cast
      rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, ← MonoidHom.range_eq_map]
      exact Nat.pos_of_ne_zero this.relIndex_ne_zero
  by_contra hfne
  obtain ⟨τ, hτ⟩ := (norm_ne_zero 𝒮ℒ f (by contrapose! hfne; ext τ; simp [hfne]) I).exists
  simp_all



end ModularForm

end

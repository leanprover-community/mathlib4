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

@[simp] lemma quotientFunc_mk (h : ℋ) : quotientFunc f ⟦h⟧ = (f : ℍ → ℂ) ∣[k] h.val⁻¹ :=
  rfl

lemma quotientFunc_smul {h} (hh : h ∈ ℋ) (q : 𝒬) :
    quotientFunc f q ∣[k] h = quotientFunc f ((⟨h, hh⟩ : ℋ)⁻¹ • q) := by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.slash_mul]

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a slash-invariant form, as a slash-invariant form. -/
@[simps! -fullyApplied]
protected def trace : SlashInvariantForm ℋ k where
  toFun := let := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _

/-- The norm of a slash-invariant form, as a slash-invariant form. -/
@[simps! -fullyApplied]
protected def norm [ℋ.HasDetPlusMinusOne] : SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := let := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _

end SlashInvariantForm

open SlashInvariantForm

section ModularForm

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a modular form, as a modular form. -/
@[simps! -fullyApplied]
protected def ModularForm.trace [ModularFormClass F 𝒢 k] : ModularForm ℋ k where
  __ := SlashInvariantForm.trace ℋ f
  holo' := .sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    rw [SlashInvariantForm.trace, IsBoundedAtImInfty, Filter.BoundedAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    refine .sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The trace of a cusp form, as a cusp form. -/
@[simps! -fullyApplied]
protected def CuspForm.trace [CuspFormClass F 𝒢 k] : CuspForm ℋ k where
  __ := ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    let := Fintype.ofFinite 𝒬
    rw [show (0 : ℂ) = ∑ c : ℋ ⧸ 𝒢.subgroupOf ℋ, 0 by simp]
    refine tendsto_finsetSum _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ ?_)
    refine (translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The norm of a modular form, as a modular form. -/
@[simps! -fullyApplied]
protected def ModularForm.norm [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm ℋ (k * Nat.card 𝒬) where
  __ := SlashInvariantForm.norm ℋ f
  holo' := .prod (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    simp_rw [SlashInvariantForm.norm, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = (fun x ↦ ∏ (i : 𝒬), 1) by ext; simp, Finset.prod_fn]
    refine .finsetProd (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

variable {f} in
lemma ModularForm.norm_ne_zero [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
    (hf : (f : ℍ → ℂ) ≠ 0) : ModularForm.norm ℋ f ≠ 0 := by
  contrapose hf
  rw [← DFunLike.coe_injective.eq_iff, coe_norm, coe_zero, prod_eq_zero_iff] at hf
  · simpa [QuotientGroup.exists_mk] using hf
  · exact Quotient.forall.mpr fun r _ ↦ (translate f r.val⁻¹).holo'

lemma ModularForm.norm_eq_zero_iff [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm.norm ℋ f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  refine ⟨fun hn ↦ ?_, fun hf ↦ ?_⟩
  · contrapose! hn
    exact norm_ne_zero ℋ hn
  · ext τ
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk]
      using ⟨1, by simpa using congr_fun hf τ⟩

open scoped MatrixGroups

lemma ModularForm.isZero_of_neg_weight [𝒢.IsArithmetic]
    {k : ℤ} (hk : k < 0) (f : ModularForm 𝒢 k) : f = 0 := by
  suffices ModularForm.norm 𝒮ℒ f = 0 by simpa [ModularForm.norm_eq_zero_iff]
  ext
  rw [ModularFormClass.levelOne_neg_weight_eq_zero
    (mul_neg_of_neg_of_pos hk <| mod_cast Nat.pos_of_ne_zero 𝒢.relIndex_ne_zero)
    (ModularForm.norm 𝒮ℒ f), Pi.zero_apply, zero_apply]

private lemma ModularForm.eq_const_of_weight_zero₀ [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (f : ModularForm 𝒢 0) : ∃ c, (f : ℍ → ℂ) = Function.const ℍ c := by
  -- Consider the norm of `f - (f I)`. This must be a constant, since it's a weight 0 level 1 form.
  let : ModularFormClass (ModularForm 𝒮ℒ (0 * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))) 𝒮ℒ 0 := by
    rw [zero_mul]; infer_instance
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.norm 𝒮ℒ (f - .const (f I)))
  -- But the constant must be 0, since `f - f I` vanishes at `I`.
  have : ModularForm.norm 𝒮ℒ (f - .const (f I)) I = 0 := by
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk] using ⟨1, by simp⟩
  obtain rfl : c = 0 := by simpa [hc]
  -- So `f - f I` has zero norm, hence it's the zero form.
  simp only [Function.const_zero, coe_eq_zero_iff, norm_eq_zero_iff, sub_eq_zero] at hc
  exact ⟨f I, by rw [hc, ModularForm.coe_const, Function.const_apply]⟩

lemma ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0) :
    ∃ c, (f : ℍ → ℂ) = Function.const ℍ c :=
  eq_const_of_weight_zero₀ (𝒢 := 𝒢 ⊓ 𝒮ℒ) {
    toFun := f
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono inf_le_left)
    slash_action_eq' γ hγ := f.slash_action_eq' γ hγ.1 }

end ModularForm

end

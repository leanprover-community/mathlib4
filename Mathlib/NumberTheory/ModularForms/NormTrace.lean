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

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
  {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

lemma IsCusp.mono {c : OnePoint ℝ} (hGH : 𝒢 ≤ ℋ) (hc : IsCusp c 𝒢) : IsCusp c ℋ :=
  match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩

lemma IsCusp.of_relindex_ne_zero {c : OnePoint ℝ} (hGH : 𝒢.relIndex ℋ ≠ 0) (hc : IsCusp c ℋ) :
    IsCusp c 𝒢 := by
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

open Pointwise in
lemma Subgroup.conjAct_pointwise_smul_iff {G : Type} [Group G] {H : Subgroup G} {g : G} :
    ConjAct.toConjAct g • H = H ↔ g ∈ normalizer H := by
  rw [← H.normalizer.inv_mem_iff]
  simp only [Subgroup.ext_iff, mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, mem_normalizer_iff, inv_inv, Iff.comm]

open Pointwise in
lemma Subgroup.conjAct_pointwise_smul_eq_self
    {G : Type} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ normalizer H) :
    ConjAct.toConjAct g • H = H :=
  Subgroup.conjAct_pointwise_smul_iff.2 hg

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

instance : MulAction ℋ ℋ := Monoid.toMulAction ..
instance : MulAction ℋ 𝒬 := .quotient ..

section SlashInvariantForm

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

lemma SlashAction.sum_slash {β G α ι : Type*} [Monoid G] [AddCommGroup α] [SlashAction β G α]
    (k : β) (g : G) {a : ι → α} {s : Finset ι} :
    (∑ i ∈ s, a i) ∣[k] g = ∑ i ∈ s, a i ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi IH => simp [hi, IH]

lemma ModularForm.prod_slash {ι : Type*} (k : ℤ) (g : GL (Fin 2) ℝ)
    {f : ι → ℍ → ℂ} {s : Finset ι} (hs : s.Nonempty) :
    (∏ i ∈ s, f i) ∣[k * s.card] g = |g.det.val| ^ (s.card - 1) • (∏ i ∈ s, f i ∣[k] g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp_all
  | insert i t hi IH =>
    by_cases ht : t.Nonempty
    · have : 0 < t.card := by aesop
      simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_succ,
        mul_add, mul_one, add_comm]
      simp [IH ht, mul_slash, show t.card + 1 - 1 = t.card - 1 + 1 by omega, pow_succ,
        ← mul_smul, mul_comm]
    · obtain rfl : t = ∅ := by simpa using ht
      simp

lemma ModularForm.prod_fintype_slash {ι : Type*} (k : ℤ) (g : GL (Fin 2) ℝ)
    {f : ι → ℍ → ℂ} [Fintype ι] [Nonempty ι] :
    (∏ i, f i) ∣[k * Fintype.card ι] g =
      |g.det.val| ^ (Fintype.card ι - 1) • (∏ i, f i ∣[k] g) := by
  simpa using ModularForm.prod_slash k g Finset.univ_nonempty

variable (ℋ)

/-- The trace of a slash-invariant form, as a slash-invariant form. -/
def SlashInvariantForm.trace [𝒢.IsFiniteRelIndex ℋ] : SlashInvariantForm ℋ k where
  toFun := letI := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    letI := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _

/-- The norm of a slash-invariant form, as a slash-invariant form. -/
@[simps]
def SlashInvariantForm.norm [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] :
    SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := letI := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    letI := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash _ _ Finset.univ_nonempty,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _

end SlashInvariantForm

section ModularForm

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a modular form, as a modular form. -/
def ModularForm.trace [ModularFormClass F 𝒢 k] : ModularForm ℋ k where
  __ := SlashInvariantForm.trace ℋ f
  holo' := by
    simp only [SlashInvariantForm.trace, SlashInvariantForm.coe_mk,
      UpperHalfPlane.mdifferentiable_iff, Function.comp_def, Finset.sum_apply]
    -- there is no `MDifferentiable.finset_sum`?
    refine DifferentiableOn.fun_sum fun q _ ↦ ?_
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
def CuspForm.trace [CuspFormClass F 𝒢 k] : CuspForm ℋ k where
  __ := ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.trace, SlashInvariantForm.trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    letI := Fintype.ofFinite 𝒬
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
    simp only [SlashInvariantForm.norm, SlashInvariantForm.coe_mk,
      UpperHalfPlane.mdifferentiable_iff, Function.comp_def, Finset.prod_apply]
    -- there is no `MDifferentiable.finset_prod`?
    refine DifferentiableOn.fun_finset_prod fun q _ ↦ ?_
    induction q using Quotient.inductionOn with | h r =>
    simpa [quotientFunc_mk, ← Function.comp_def (f := f ∣[k] r.val⁻¹),
      ← UpperHalfPlane.mdifferentiable_iff] using (ModularForm.translate f r.val⁻¹).holo'
  bdd_at_cusps' h γ := by
    rintro rfl
    letI := Fintype.ofFinite 𝒬
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

lemma UpperHalfPlane.eq_zero_of_frequently {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {τ : ℍ} (hτ : ∃ᶠ z in 𝓝[≠] τ, f z = 0) : f = 0 := by
  let F : ℂ → ℂ := f ∘ .ofComplex
  rw [UpperHalfPlane.mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  have := this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ ?_ ?_
  · ext w
    convert this w.property
    rw [Function.comp_apply, ofComplex_apply_of_im_pos]
    rfl
  · apply IsConnected.isPreconnected
    apply Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)
  · exact τ.property
  · contrapose! hτ
    rw [eventually_nhdsWithin_iff, ← isOpenEmbedding_coe.map_nhds_eq,
      Filter.eventually_map] at hτ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hτ] with a ha
    simp_all

lemma normMF_ne_zero [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
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

lemma isZero_of_neg_weight (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] {k : ℤ} (hk : k < 0)
    (f : ModularForm Γ k) : f = 0 := by
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
  have : PerfectSpace ℍ := by
    constructor
    apply isPreconnected_univ.preperfect_of_nontrivial
    rw [Set.nontrivial_univ_iff]
    -- this should be an instance?
    use I, ⟨2 * Complex.I, by simp⟩
    simp [UpperHalfPlane.ext_iff]
  by_contra hfne
  obtain ⟨τ, hτ⟩ := (normMF_ne_zero 𝒮ℒ f (by contrapose! hfne; ext τ; simp [hfne]) I).exists
  simp_all

end ModularForm

end

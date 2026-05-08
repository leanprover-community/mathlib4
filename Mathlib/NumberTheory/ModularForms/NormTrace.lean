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

/-- Each `quotientFunc f q` is holomorphic on the upper half plane. -/
lemma quotientFunc_mdiff [ModularFormClass F 𝒢 k] (q : 𝒬) :
    MDiff (quotientFunc f q) :=
  Quotient.inductionOn q fun r => (ModularForm.translate f r.val⁻¹).holo'

/-- Each `quotientFunc f q` is bounded at `∞`. -/
lemma quotientFunc_isBoundedAtImInfty [ModularFormClass F 𝒢 k] [𝒢.IsFiniteRelIndex ℋ]
    [Fact (IsCusp OnePoint.infty ℋ)] (q : 𝒬) :
    IsBoundedAtImInfty (quotientFunc f q) :=
  Quotient.inductionOn q fun ⟨_, hr⟩ => OnePoint.isBoundedAt_infty_iff.mp <|
    (ModularForm.translate f _).bdd_at_cusps'
      ((Fact.out : IsCusp _ _).of_isFiniteRelIndex_conj hr)

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

namespace ModularForm

section GaloisProd

variable (N : ℕ) (f : ℍ → ℂ)

/-- The product `∏_{j < N} f(τ - j)`, used as a building block of the norm map. -/
noncomputable def galoisProd (τ : ℍ) : ℂ :=
  ∏ j ∈ Finset.range N, f (ofComplex ((τ : ℂ) - j))

variable {N f}

/-- If `f` has period `N` along `ofComplex`, then `galoisProd N f` has period `1`. -/
lemma galoisProd_periodic_one (hN : 0 < N)
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ)) :
    Function.Periodic (galoisProd N f ∘ ofComplex) 1 := by
  intro w
  simp only [Function.comp_apply]
  unfold galoisProd
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    rw [ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw,
      Finset.prod_range_succ' (fun j => f (ofComplex (w + 1 - ↑j))),
      Finset.prod_range_succ (fun j => f (ofComplex (w - ↑j)))]
    have hinner : ∏ j ∈ Finset.range n, f (ofComplex (w + 1 - ↑(j + 1))) =
        ∏ j ∈ Finset.range n, f (ofComplex (w - ↑j)) :=
      Finset.prod_congr rfl fun j _ => by
        congr 2
        push_cast
        ring
    have hbdry : f (ofComplex (w + 1 - ↑(0 : ℕ))) = f (ofComplex (w - ↑n)) := by
      rw [show w + 1 - ↑(0 : ℕ) = (w - ↑n) + ↑(n + 1 : ℕ) by push_cast; ring]
      exact hf_per (w - ↑n)
    rw [hinner, hbdry]
  · have hw0 : w.im ≤ 0 := not_lt.mp hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw0
    rw [ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw0]

/-- If `f` is holomorphic on `ℍ`, so is `galoisProd N f`. -/
lemma galoisProd_mdiff (hf_mdiff : MDiff f) : MDiff (galoisProd N f) := by
  unfold galoisProd
  have hfo : DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
    mdifferentiable_iff.mp hf_mdiff
  intro τ
  rw [mdifferentiableAt_iff]
  have hτj : ∀ j : ℕ, 0 < ((τ : ℂ) - ↑j).im := fun j => by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  refine DifferentiableAt.fun_finsetProd fun j _ =>
    DifferentiableAt.congr_of_eventuallyEq
      (((hfo ((τ : ℂ) - j) (hτj j)).differentiableAt
        (isOpen_upperHalfPlaneSet.mem_nhds (hτj j))).comp (τ : ℂ)
        ((differentiableAt_id (𝕜 := ℂ)).sub (differentiableAt_const (c := (j : ℂ))))) ?_
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp_all [Function.comp_apply, id_eq, Pi.sub_apply]

/-- If `f` is bounded at `i∞`, so is `galoisProd N f`. -/
lemma galoisProd_isBoundedAtImInfty (hf_bdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (galoisProd N f) := by
  unfold galoisProd IsBoundedAtImInfty Filter.BoundedAtFilter
  rw [← Finset.prod_fn]
  refine Filter.BoundedAtFilter.prod _ fun j _ => hf_bdd.comp_tendsto ?_
  simp only [atImInfty, Filter.tendsto_comap_iff, Function.comp_def]
  refine Filter.tendsto_comap.congr' (.of_forall fun τ => ?_)
  have him : 0 < ((τ : ℂ) - ↑j).im := by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  simp [ofComplex_apply_of_im_pos him]

/-- The cusp function of `galoisProd N f` (period `1`) at `q^N` factors as a product of `N` shifted
copies of the cusp function of `f` (period `N`). -/
lemma cuspFunction_one_galoisProd_pow_eq (hN : 0 < N)
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ))
    (hf_bdd : IsBoundedAtImInfty f) (hf_mdiff : MDiff f) :
    (fun q : ℂ => cuspFunction 1 (galoisProd N f) (q ^ N))
      =ᶠ[𝓝 0]
    (fun q : ℂ => ∏ j ∈ Finset.range N,
      cuspFunction (N : ℝ) f (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR_ne : (N : ℝ) ≠ 0 := hNR.ne'
  have hNC_ne : (N : ℂ) ≠ 0 := mod_cast hN.ne'
  have hRHS_an : AnalyticAt ℂ (cuspFunction (N : ℝ) f) 0 :=
    analyticAt_cuspFunction_zero hNR hf_per hf_mdiff hf_bdd
  have hLHS_cts : ContinuousAt
      (fun q : ℂ => cuspFunction 1 (galoisProd N f) (q ^ N)) 0 :=
    (analyticAt_cuspFunction_zero one_pos (galoisProd_periodic_one hN hf_per)
      (galoisProd_mdiff hf_mdiff) (galoisProd_isBoundedAtImInfty hf_bdd)).continuousAt.comp_of_eq
      (by fun_prop) (by simp [zero_pow hN.ne'])
  have h_factor_cts : ∀ j ∈ Finset.range N, ContinuousAt
      (fun q : ℂ => cuspFunction (N : ℝ) f
        (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 := fun _ _ =>
    hRHS_an.continuousAt.comp_of_eq (by fun_prop) (by simp)
  have hRHS_cts : ContinuousAt
      (fun q : ℂ => ∏ j ∈ Finset.range N,
        cuspFunction (N : ℝ) f (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 :=
    tendsto_finsetProd _ fun j hj => (h_factor_cts j hj).tendsto
  rw [← hLHS_cts.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hRHS_cts,
    eventuallyEq_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq_lt hq_ne
  rw [mem_ball_zero_iff] at hq_lt
  set τ : ℍ := ⟨Function.Periodic.invQParam (N : ℝ) q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one hNR hq_lt hq_ne⟩
  have hτq : Function.Periodic.qParam (N : ℝ) τ = q :=
    Function.Periodic.qParam_right_inv hNR_ne hq_ne
  have hqN : q ^ N = Function.Periodic.qParam 1 (τ : ℂ) := by
    rw [← hτq]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_one, div_one,
      Complex.ofReal_natCast]
    congr 1
    field_simp
  rw [hqN, eq_cuspFunction τ one_ne_zero (galoisProd_periodic_one hN hf_per)]
  unfold galoisProd
  refine Finset.prod_congr rfl fun j _ => ?_
  have him : 0 < ((τ : ℂ) - ↑j).im := by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  have hqj : q * Complex.exp (-2 * Real.pi * Complex.I * j / N) =
      Function.Periodic.qParam (N : ℝ) ((⟨(τ : ℂ) - j, him⟩ : ℍ) : ℂ) := by
    rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by push_cast; rfl, ← hτq,
      ← Function.Periodic.qParam_sub (h := (N : ℝ)) τ j]
  rw [hqj, eq_cuspFunction ⟨(τ : ℂ) - j, him⟩ hNR_ne hf_per, ofComplex_apply_of_im_pos him]

/-- The q-expansion of `galoisProd N f` (period `1`) and that of `f` (period `N`) have the same
order at `0`. -/
lemma qExpansion_one_galoisProd_order_eq_qExpansion_self_order (hN : 0 < N)
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ))
    (hf_bdd : IsBoundedAtImInfty f) (hf_mdiff : MDiff f) :
    (qExpansion 1 (galoisProd N f)).order = (qExpansion (N : ℝ) f).order := by
  have hLHS_an : AnalyticAt ℂ (cuspFunction 1 (galoisProd N f)) 0 :=
    analyticAt_cuspFunction_zero one_pos (galoisProd_periodic_one hN hf_per)
      (galoisProd_mdiff hf_mdiff) (galoisProd_isBoundedAtImInfty hf_bdd)
  have hRHS_an : AnalyticAt ℂ (cuspFunction (N : ℝ) f) 0 :=
    analyticAt_cuspFunction_zero (mod_cast hN) hf_per hf_mdiff hf_bdd
  rw [qExpansion_order_eq_analyticOrderAt_cuspFunction hLHS_an,
    qExpansion_order_eq_analyticOrderAt_cuspFunction hRHS_an]
  set ML := analyticOrderAt (cuspFunction 1 (galoisProd N f)) 0
  set MR := analyticOrderAt (cuspFunction (N : ℝ) f) 0
  have h_factor_an : ∀ j ∈ Finset.range N,
      AnalyticAt ℂ (fun q : ℂ => cuspFunction (N : ℝ) f
        (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 := fun j _ =>
    hRHS_an.comp_of_eq (by fun_prop) (by simp)
  have h_factor_order : ∀ j ∈ Finset.range N,
      analyticOrderAt (fun q : ℂ => cuspFunction (N : ℝ) f
        (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 = MR := fun j _ => by
    rw [← Function.comp_def, analyticOrderAt_comp_of_deriv_ne_zero
      (f := cuspFunction (N : ℝ) f) (by fun_prop) (by simp [Complex.exp_ne_zero]), zero_mul]
  have h_combine : ML * (N : ℕ∞) = (N : ℕ∞) * MR := by
    rw [← analyticOrderAt_comp_pow_zero hLHS_an hN,
      analyticOrderAt_congr (cuspFunction_one_galoisProd_pow_eq hN hf_per hf_bdd hf_mdiff),
      ← Finset.prod_fn, analyticOrderAt_prod h_factor_an,
      Finset.sum_congr rfl h_factor_order, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN_ne : (N : ℕ∞) ≠ 0 := mod_cast hN.ne'
  clear_value ML MR
  rcases eq_or_ne ML ⊤ with hL | hL <;> rcases eq_or_ne MR ⊤ with hR | hR
  · rw [hL, hR]
  · lift MR to ℕ using hR
    rw [hL, ENat.top_mul hN_ne] at h_combine
    exact absurd h_combine.symm (ENat.coe_ne_top _)
  · lift ML to ℕ using hL
    rw [hR, ENat.mul_top hN_ne] at h_combine
    exact absurd h_combine (ENat.coe_ne_top _)
  · lift ML to ℕ using hL
    lift MR to ℕ using hR
    rw [mul_comm (N : ℕ∞)] at h_combine
    exact_mod_cast Nat.eq_of_mul_eq_mul_right hN (mod_cast h_combine)

end GaloisProd

section NormDecomposition

open scoped MatrixGroups

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ] {k : ℤ}
  (f : ModularForm 𝒢 k)

/-- The value of `quotientFunc f` at the coset of `T^j` is `f (τ - j)`. -/
lemma quotientFunc_T_pow_apply
    (j : Fin 𝒢.integerCuspWidth) (τ : ℍ) :
    SlashInvariantForm.quotientFunc f
        (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
            ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
          𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) τ =
      f (ofComplex ((τ : ℂ) - j)) := by
  rw [SlashInvariantForm.quotientFunc_mk]
  have h_val : ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
      ((ModularGroup.T : SL(2, ℤ))^(j : ℕ)) : 𝒮ℒ).val =
      ((ModularGroup.T : SL(2, ℤ))^(j : ℕ) : GL (Fin 2) ℝ) := by
    rw [MonoidHom.coe_rangeRestrict, map_pow]
    rfl
  rw [h_val,
    show (((ModularGroup.T : SL(2, ℤ))^(j : ℕ) : GL (Fin 2) ℝ))⁻¹ =
      ((ModularGroup.T : SL(2, ℤ))^(-(j : ℕ) : ℤ) : GL (Fin 2) ℝ) by
      rw [zpow_neg, zpow_natCast],
    SlashInvariantForm.slash_T_zpow_apply_general _ _ _ τ]
  have him : 0 < ((τ : ℂ) - (j : ℂ)).im := by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  have h_eq : ((-(j : ℕ) : ℝ) +ᵥ τ : ℍ) = ofComplex ((τ : ℂ) - (j : ℂ)) := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos him]
    push_cast
    ring
  rw [show ((-((j : ℕ) : ℤ) : ℤ) : ℝ) = (-(j : ℕ) : ℝ) by push_cast; ring, h_eq]

/-- Left-multiplication by the coset of `T` permutes the image of the `T^j` cosets. -/
lemma image_T_pow_invariant_under_T_mul
    [DiscreteTopology 𝒢.strictPeriods]
    [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] {x : 𝒮ℒ}
    (hx : (⟦x⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) ∈
        Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
          (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
              ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
            𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)))) :
    (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)) * x⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) ∈
      Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
        (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
            ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
          𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  classical
  set T_𝒮ℒ : 𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
    (ModularGroup.T : SL(2, ℤ)) with hT_𝒮ℒ_def
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_image, show (⟦T_𝒮ℒ * x⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) =
      ⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
          ((ModularGroup.T : SL(2, ℤ))^((j : ℕ) + 1))⟧ by
    rw [pow_succ', map_mul, hT_𝒮ℒ_def.symm, QuotientGroup.eq]
    convert inv_mem (QuotientGroup.eq.mp hj) using 1
    group]
  by_cases hj1 : (j : ℕ) + 1 < 𝒢.integerCuspWidth
  · exact ⟨⟨(j : ℕ) + 1, hj1⟩, Finset.mem_univ _, rfl⟩
  · have hj_eq : (j : ℕ) + 1 = 𝒢.integerCuspWidth := by
      have := j.isLt
      omega
    refine ⟨⟨0, Subgroup.integerCuspWidth_pos⟩, Finset.mem_univ _, ?_⟩
    rw [hj_eq, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using Subgroup.T_zpow_integerCuspWidth_mem (𝒢 := 𝒢)

/-- The action of `T` (via `mapGL`) on `𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ)` permutes the image of the `T^j` cosets. -/
lemma image_T_pow_invariant_under_T_smul
    [DiscreteTopology 𝒢.strictPeriods]
    [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    {q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)}
    (hq : q ∈ Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
        (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
            ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
          𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)))) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)) • q :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) ∈
      Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
        (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
            ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
          𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  induction q using Quotient.inductionOn with
  | h x => exact image_T_pow_invariant_under_T_mul (𝒢 := 𝒢) hq

/-- Left-multiplication by the inverse of the coset of `T` preserves membership in the image of
the `T^j` cosets. -/
lemma image_T_pow_smul_inv_iff
    [DiscreteTopology 𝒢.strictPeriods]
    [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    (q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)))⁻¹ • q ∈
        Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
          (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
              ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
            𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) ↔
      q ∈ Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
        (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
            ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
          𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  letI : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  set T_𝒮ℒ : 𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
    (ModularGroup.T : SL(2, ℤ))
  set image : Finset (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :=
    Finset.univ.image (fun j : Fin 𝒢.integerCuspWidth =>
      (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
          ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) with himage_def
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · have h := image_T_pow_invariant_under_T_smul (𝒢 := 𝒢) hq
    rwa [smul_inv_smul] at h
  · have h_inj : Function.Injective
        (fun q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ) => T_𝒮ℒ • q) :=
      MulAction.injective T_𝒮ℒ
    have h_smul_image : image.image (fun q => T_𝒮ℒ • q) = image := by
      refine Finset.eq_of_subset_of_card_le (fun q hq' => ?_) ?_
      · obtain ⟨q', hq'', rfl⟩ := Finset.mem_image.mp hq'
        exact image_T_pow_invariant_under_T_smul (𝒢 := 𝒢) hq''
      · rw [Finset.card_image_of_injective _ h_inj]
    have h_target : T_𝒮ℒ • (T_𝒮ℒ⁻¹ • q) ∈ image := by
      rwa [smul_inv_smul]
    obtain ⟨q', hq'_mem, hq'_eq⟩ := Finset.mem_image.mp (h_smul_image ▸ h_target)
    exact h_inj hq'_eq ▸ hq'_mem

/-- The product of `quotientFunc f q` over the cosets `q` not in the image of `T^j` is invariant
under `τ ↦ τ + 1`. -/
lemma prod_quotientFunc_filter_image_one_vadd
    [DiscreteTopology 𝒢.strictPeriods]
    [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    [Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    (τ : ℍ) :
    (∏ q ∈ Finset.univ.filter (· ∉ Finset.univ.image
          (fun j : Fin 𝒢.integerCuspWidth =>
            (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
                ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
              𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)))),
        SlashInvariantForm.quotientFunc f q ((1 : ℝ) +ᵥ τ)) =
      ∏ q ∈ Finset.univ.filter (· ∉ Finset.univ.image
          (fun j : Fin 𝒢.integerCuspWidth =>
            (⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
                ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
              𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)))),
        SlashInvariantForm.quotientFunc f q τ := by
  set T_𝒮ℒ : 𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
    (ModularGroup.T : SL(2, ℤ))
  have h_step1 (q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :
      SlashInvariantForm.quotientFunc f q ((1 : ℝ) +ᵥ τ) =
        SlashInvariantForm.quotientFunc f (T_𝒮ℒ⁻¹ • q) τ := by
    rw [show (SlashInvariantForm.quotientFunc f q) ((1 : ℝ) +ᵥ τ) =
          ((SlashInvariantForm.quotientFunc f q) ∣[k] T_𝒮ℒ.val) τ by
        simpa [zpow_one] using
          (SlashInvariantForm.slash_T_zpow_apply_general k 1 (SlashInvariantForm.quotientFunc f q)
            τ).symm,
      SlashInvariantForm.quotientFunc_smul f T_𝒮ℒ.2]
  refine (Finset.prod_congr rfl fun q _ => h_step1 q).trans <|
    Finset.prod_equiv (MulAction.toPerm T_𝒮ℒ⁻¹)
      (fun q => by simpa using (image_T_pow_smul_inv_iff (𝒢 := 𝒢) q).symm.not)
      (fun _ _ => rfl)

/-- Decomposition of the norm of `f` at the cusp `∞`: `(norm f) τ` equals the product of
`f (ofComplex (τ - j))` for `j < integerCuspWidth 𝒢` times an analytic remainder term. -/
lemma analyticAt_cuspFunction_one_norm_rest
    [DiscreteTopology 𝒢.strictPeriods] :
    ∃ rest : ℍ → ℂ,
      Function.Periodic (rest ∘ ofComplex) 1 ∧
      AnalyticAt ℂ (cuspFunction 1 rest) 0 ∧
      ∀ τ : ℍ, (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) τ =
        (∏ j ∈ Finset.range 𝒢.integerCuspWidth, f (ofComplex ((τ : ℂ) - j))) * rest τ := by
  classical
  set h_𝒢 := 𝒢.integerCuspWidth
  letI : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  set imgFn : Fin h_𝒢 → 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ) := fun j =>
    ⟦(Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
        ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧
  set image : Finset (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :=
    Finset.univ.image imgFn with himage_def
  have h_imgFn_inj : Function.Injective imgFn :=
    Subgroup.quotient_T_pow_injective_integerCuspWidth (𝒢 := 𝒢)
  let rest : ℍ → ℂ := fun τ =>
    ∏ q ∈ Finset.univ.filter (· ∉ image), SlashInvariantForm.quotientFunc f q τ
  have h_rest_eq : (rest : ℍ → ℂ) =
      ∏ q ∈ Finset.univ.filter (· ∉ image), SlashInvariantForm.quotientFunc f q :=
    funext fun _ => (Finset.prod_apply ..).symm
  have h_rest_mdiff : MDiff rest :=
    h_rest_eq ▸ MDifferentiable.prod fun q _ => SlashInvariantForm.quotientFunc_mdiff f q
  have h_rest_bdd : IsBoundedAtImInfty rest :=
    h_rest_eq ▸ Filter.BoundedAtFilter.prod _ fun q _ =>
      SlashInvariantForm.quotientFunc_isBoundedAtImInfty f q
  have h_rest_periodic : Function.Periodic (rest ∘ ofComplex) 1 := fun w => by
    simp only [Function.comp_apply]
    by_cases! hw : 0 < w.im
    · have hw1 : 0 < (w + 1).im := by simpa using hw
      rw [ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw,
        show (⟨w + 1, hw1⟩ : ℍ) = ((1 : ℝ) +ᵥ (⟨w, hw⟩ : ℍ) : ℍ) from
          UpperHalfPlane.ext (by simp [add_comm])]
      exact prod_quotientFunc_filter_image_one_vadd f ⟨w, hw⟩
    · rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hw) hw]
  refine ⟨rest, h_rest_periodic,
    analyticAt_cuspFunction_zero one_pos h_rest_periodic h_rest_mdiff h_rest_bdd, fun τ => ?_⟩
  rw [ModularForm.coe_norm, Finset.prod_apply,
    ← Finset.prod_filter_mul_prod_filter_not _ (· ∈ image), Finset.filter_univ_mem,
    himage_def, Finset.prod_image h_imgFn_inj.injOn,
    Finset.prod_congr rfl fun j _ => quotientFunc_T_pow_apply f j τ,
    Fin.prod_univ_eq_prod_range (fun n => f (ofComplex ((τ : ℂ) - (n : ℕ)))) h_𝒢]

end NormDecomposition

end ModularForm

end

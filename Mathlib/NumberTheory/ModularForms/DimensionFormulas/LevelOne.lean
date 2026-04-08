/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Dimension formula for level 1 modular forms

This file proves the dimension formula for the space of modular forms for `𝒮ℒ` (= `SL(2, ℤ)`)
of even weight `k ≥ 3`.

## Main results

* `CuspForm.discriminantEquiv`: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.
* `ModularForm.rank_eq_one_add_rank_cuspForm`: `rank M_k = 1 + rank S_k` for even `k ≥ 3`.
* `ModularForm.dimension_level_one`: the full dimension formula.
-/

open UpperHalfPlane ModularForm Complex SlashInvariantForm SlashInvariantFormClass
  ModularFormClass CongruenceSubgroup MatrixGroups OnePoint Filter Topology EisensteinSeries

noncomputable section

/-! ### Delta isomorphism: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)` -/

section DeltaIsomorphism

variable {k : ℤ}

local notation "Δ" => ModularForm.discriminant

namespace CuspForm

/-- Multiply a modular form of weight `k - 12` by the discriminant to get a cusp form of
weight `k`. Built directly as a CuspForm (no `IsCuspForm` intermediary). -/
def ofMulDiscriminant (f : ModularForm 𝒮ℒ (k - 12)) : CuspForm 𝒮ℒ k :=
  let Δ' := CuspForm.toModularFormₗ discriminantCuspForm
  ModularForm.toCuspForm (ModularForm.mcast (by ring) (f.mul Δ')) (by
    have hΔ' : (qExpansion 1 (Δ' : ℍ → ℂ)).coeff 0 = 0 :=
      (qExpansion_coeff_zero Δ' one_pos one_mem_strictPeriods_SL).trans
        (CuspFormClass.zero_at_infty discriminantCuspForm).valueAtInfty_eq_zero
    rw [show (ModularForm.mcast _ (f.mul Δ') : ℍ → ℂ) = (f : ℍ → ℂ) * Δ' from rfl,
      qExpansion_mul_coeff_zero
        (analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL).continuousAt
        (analyticAt_cuspFunction_zero Δ' one_pos one_mem_strictPeriods_SL).continuousAt,
      hΔ', mul_zero])

@[simp]
lemma ofMulDiscriminant_apply (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ) :
    (ofMulDiscriminant f) z = f z * Δ z := rfl

private lemma divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (fun z ↦ f z / Δ z) ∣[k - 12] γ = fun z ↦ f z / Δ z := by
  haveI : SlashInvariantFormClass (CuspForm 𝒮ℒ k) (CongruenceSubgroup.Gamma 1) k :=
    CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ inferInstance
  haveI : SlashInvariantFormClass (CuspForm 𝒮ℒ 12) (CongruenceSubgroup.Gamma 1) 12 :=
    CongruenceSubgroup.Gamma_one_coe_eq_SL ▸ inferInstance
  have hf := slash_action_eqn_SL'' f (mem_Gamma_one γ)
  have hΔ := slash_action_eqn_SL'' discriminantCuspForm (mem_Gamma_one γ)
  ext z
  rw [SL_slash_apply, hf, show Δ (γ • z) = denom γ z ^ (12 : ℤ) * Δ z from by
    exact_mod_cast hΔ z]
  have hd : (denom γ z : ℂ) ≠ 0 := denom_ne_zero γ z
  rw [div_mul_eq_mul_div, mul_right_comm, ← zpow_add₀ hd,
    show k + -(k - 12) = (12 : ℤ) from by ring]
  exact mul_div_mul_left (f z) (Δ z) (zpow_ne_zero _ hd)

private lemma exp_decay_isBigO_discriminant (f : CuspForm 𝒮ℒ k) :
    (f : ℍ → ℂ) =O[atImInfty] Δ := by
  have hf_decay := CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL
  have hΔ_lower : ∀ᶠ τ : ℍ in atImInfty,
      ‖(fun τ : ℍ ↦ Real.exp (-2 * Real.pi * τ.im / 1)) τ‖ ≤ 2 * ‖Δ τ‖ := by
    have hprod := discriminant_bounded_factor.eventually
      (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1/2))
    filter_upwards [hprod] with τ hτ
    simp only [div_one]
    rw [discriminant_eq_q_prod, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hq_norm : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ =
        Real.exp (-2 * Real.pi * τ.im) := by
      simp [Function.Periodic.qParam, Complex.norm_exp, Complex.mul_re, div_one]
    rw [← hq_norm]
    have hprod_bound : 1 / 2 ≤ ‖∏' (n : ℕ), (1 - eta_q n τ) ^ 24‖ := by
      have hsub : ‖∏' (n : ℕ), (1 - eta_q n τ) ^ 24 - 1‖ < 1 / 2 := by
        rwa [Complex.dist_eq] at hτ
      have h1 := norm_sub_norm_le (1 : ℂ) (∏' (n : ℕ), (1 - eta_q n τ) ^ 24)
      simp only [norm_one] at h1
      linarith [norm_sub_rev (1 : ℂ) (∏' (n : ℕ), (1 - eta_q n τ) ^ 24)]
    linarith [norm_nonneg (Function.Periodic.qParam 1 (τ : ℂ)),
      mul_le_mul_of_nonneg_left hprod_bound
        (norm_nonneg (Function.Periodic.qParam 1 (τ : ℂ)))]
  exact hf_decay.trans (Asymptotics.IsBigO.of_bound 2 hΔ_lower)

/-- Divide a cusp form by the discriminant to get a modular form of weight `k - 12`. -/
def divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) where
  toFun z := f z / Δ z
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact divByDiscriminant_slash_eq f γ
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (UpperHalfPlane.mdifferentiable_iff.mp f.holo').div
      (UpperHalfPlane.mdifferentiable_iff.mp discriminantCuspForm.holo') fun z hz ↦ ?_
    simpa [ofComplex_apply_of_im_pos hz] using discriminant_ne_zero ⟨z, hz⟩
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [divByDiscriminant_slash_eq f γ, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO
      (exp_decay_isBigO_discriminant f)).isBigO_one ℝ

@[simp]
lemma divDiscriminant_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (divDiscriminant f) z = f z / Δ z := rfl

/-- The linear equivalence between cusp forms of weight `k` and modular forms of weight `k - 12`,
given by division by the discriminant. -/
def discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12) where
  toFun := divDiscriminant
  map_add' a b := by ext z; simp [add_div]
  map_smul' c a := by ext z; simp [mul_div_assoc]
  invFun := ofMulDiscriminant
  left_inv f := by
    ext z
    simp only [divDiscriminant_apply, ofMulDiscriminant_apply]
    exact div_mul_cancel₀ (f z) (discriminant_ne_zero z)
  right_inv f := by
    ext z
    simp only [ofMulDiscriminant_apply, divDiscriminant_apply]
    exact mul_div_cancel_right₀ (f z) (discriminant_ne_zero z)

end CuspForm

end DeltaIsomorphism

/-! ### Rank identities -/

section RankIdentity

variable {k : ℤ}

/-- Cusp forms of weight `k < 12` for `𝒮ℒ` are zero-dimensional. -/
lemma cuspForm_rank_lt_twelve (hk : k < 12) :
    Module.rank ℂ (CuspForm 𝒮ℒ k) = 0 := by
  rw [LinearEquiv.rank_eq CuspForm.discriminantEquiv]
  exact levelOne_neg_weight_rank_zero (by omega)

/-- The space of weight 12 cusp forms for `𝒮ℒ` has rank 1. -/
lemma cuspForm_rank_twelve : Module.rank ℂ (CuspForm 𝒮ℒ 12) = 1 := by
  rw [LinearEquiv.rank_eq CuspForm.discriminantEquiv,
    show (12 : ℤ) - 12 = 0 from by norm_num]
  exact levelOne_weight_zero_rank_one

/-- Every weight 12 cusp form for `𝒮ℒ` is a scalar multiple of the discriminant. -/
lemma cuspForm_twelve_smul_discriminant (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • discriminantCuspForm = f := by
  have hne : discriminantCuspForm ≠ 0 := fun h ↦
    discriminant_ne_zero UpperHalfPlane.I (congr_fun (congr_arg DFunLike.coe h) _)
  exact (finrank_eq_one_iff_of_nonzero' discriminantCuspForm hne).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp cuspForm_rank_twelve) f

/-- For even `k ≥ 3`, the rank of `𝒮ℒ` modular forms is one more than the rank of
cusp forms. -/
lemma ModularForm.rank_eq_one_add_rank_cuspForm {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ (k : ℤ)) = 1 + Module.rank ℂ (CuspForm 𝒮ℒ (k : ℤ)) := by
  have h_add := Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ (k : ℤ))
  rw [show Module.rank ℂ ↥(cuspFormSubmodule 𝒮ℒ (k : ℤ)) =
    Module.rank ℂ (CuspForm 𝒮ℒ (k : ℤ)) from
    (LinearEquiv.rank_eq (CuspForm.equivCuspFormSubmodule 𝒮ℒ (k : ℤ))).symm] at h_add
  suffices h1 : Module.rank ℂ (ModularForm 𝒮ℒ (k : ℤ) ⧸ cuspFormSubmodule 𝒮ℒ (k : ℤ)) = 1 by
    rw [← h_add, h1]
  have hE_coeff_zero := E_qExpansion_coeff_zero hk hk2
  apply rank_eq_one (Submodule.Quotient.mk (p := cuspFormSubmodule 𝒮ℒ (k : ℤ)) (E hk))
  · intro h
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact one_ne_zero <|
      hE_coeff_zero.symm.trans <|
      (isCuspForm_iff_coeffZero_eq_zero _).mp h
  · refine (Submodule.Quotient.mk_surjective _).forall.mpr fun f ↦
      ⟨(qExpansion 1 f).coeff 0, ?_⟩
    have h_mem : f - (qExpansion 1 ↑f).coeff 0 • E hk ∈
        cuspFormSubmodule 𝒮ℒ (k : ℤ) :=
      (isCuspForm_iff_coeffZero_eq_zero _).mpr (by
        set c := (qExpansion 1 ↑f).coeff 0 with hc
        have hsub := (qExpansionAddHom one_pos one_mem_strictPeriods_SL (k := (k : ℤ))).map_sub
          f (c • E hk)
        simp only [qExpansionAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hsub
        rw [hsub]
        have hcoe : ⇑(c • E hk) = c • (E hk : ℍ → ℂ) := rfl
        rw [hcoe, qExpansion_smul one_pos one_mem_strictPeriods_SL c (E hk)]
        simp only [_root_.map_sub, _root_.map_smul, smul_eq_mul, hE_coeff_zero, mul_one, ← hc,
          sub_self])
    have h0 : ((cuspFormSubmodule 𝒮ℒ (k : ℤ)).mkQ (f - (qExpansion 1 ↑f).coeff 0 •
        E hk) : ModularForm 𝒮ℒ (k : ℤ) ⧸ cuspFormSubmodule 𝒮ℒ (k : ℤ)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h_mem
    rw [map_sub, LinearMap.map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
      sub_eq_zero] at h0
    exact h0.symm

end RankIdentity

/-! ### Dimension formula -/

section DimensionFormula

/-! ### Helpers for weight 2 proof -/

/-- In a rank-one ℂ-module, every element is a scalar multiple of any nonzero element.
This is a thin wrapper around `finrank_eq_one_iff_of_nonzero'` adapted to `Module.rank`. -/
private lemma exists_smul_eq_of_rank_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hrank : Module.rank ℂ M = 1) {e : M} (he : e ≠ 0) (f : M) : ∃ c : ℂ, c • e = f :=
  (finrank_eq_one_iff_of_nonzero' e he).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) f

/-- Weight 4 modular forms for `𝒮ℒ` are 1-dimensional. -/
private lemma weight_four_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ (4 : ℤ)) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (cuspForm_rank_lt_twelve (by norm_num))).trans (by norm_cast))

/-- Weight 6 modular forms for `𝒮ℒ` are 1-dimensional. -/
private lemma weight_six_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ (6 : ℤ)) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (cuspForm_rank_lt_twelve (by norm_num))).trans (by norm_cast))

private lemma E_qExpansion_coeff_one_four :
    (qExpansion 1 (E (show 3 ≤ 4 by norm_num))).coeff 1 = 240 := by
  rw [E_qExpansion_coeff (show 3 ≤ 4 by norm_num) ⟨2, rfl⟩]
  simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte]
  rw [show bernoulli (4 : ℕ) = ((-1 : ℚ) / 30 : ℚ) from by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]; exact bernoulli'_four]
  simp [ArithmeticFunction.sigma_one]; norm_num

private lemma E_qExpansion_coeff_one_six :
    (qExpansion 1 (E (show 3 ≤ 6 by norm_num))).coeff 1 = -504 := by
  rw [E_qExpansion_coeff (show 3 ≤ 6 by norm_num) ⟨3, rfl⟩]
  simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte]
  rw [show bernoulli (6 : ℕ) = ((1 : ℚ) / 42 : ℚ) from by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero,
      show Nat.choose 6 2 = 15 from by decide, show Nat.choose 6 4 = 15 from by decide,
      bernoulli'_eq_zero_of_odd (show Odd 5 from ⟨2, rfl⟩) (by norm_num)]]
  simp [ArithmeticFunction.sigma_one]; norm_num

/-- The modular discriminant equals `(E₄³ - E₆²) / 1728`. -/
theorem ModularForm.discriminant_eq_E4_cube_sub_E6_sq (z : ℍ) :
    discriminant z = (1 / 1728) *
      (E (show 3 ≤ 4 by norm_num) z ^ 3 - E (show 3 ≤ 6 by norm_num) z ^ 2) := by
  set E4 := E (show 3 ≤ 4 by norm_num)
  set E6 := E (show 3 ≤ 6 by norm_num)
  set F : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (show 4 + (4 + 4) = 12 by norm_num)
      (E4.mul (ModularForm.mcast (show 4 + 4 = 4 + 4 from rfl) (E4.mul E4))) -
    ModularForm.mcast (show 6 + 6 = 12 by norm_num) (E6.mul E6)
  have hF : ∀ w, F w = E4 w ^ 3 - E6 w ^ 2 := fun w ↦ by
    change E4 w * (E4 w * E4 w) - E6 w * E6 w = E4 w ^ 3 - E6 w ^ 2; ring
  have h0_4 := E_qExpansion_coeff_zero (show 3 ≤ 4 by norm_num) ⟨2, rfl⟩
  have h0_6 := E_qExpansion_coeff_zero (show 3 ≤ 6 by norm_num) ⟨3, rfl⟩
  have hF_cusp : IsCuspForm F := (isCuspForm_iff_coeffZero_eq_zero F).mpr (by
    rw [qExpansion_coeff_zero F one_pos one_mem_strictPeriods_SL]
    have hv4 : valueAtInfty (E4 : ℍ → ℂ) = 1 := by
      rwa [← qExpansion_coeff_zero E4 one_pos one_mem_strictPeriods_SL]
    have hv6 : valueAtInfty (E6 : ℍ → ℂ) = 1 := by
      rwa [← qExpansion_coeff_zero E6 one_pos one_mem_strictPeriods_SL]
    change limUnder atImInfty (fun w ↦ E4 w * (E4 w * E4 w) - E6 w * E6 w) = 0
    have htend : ∀ (k' : ℤ) (f : ModularForm 𝒮ℒ k') (c' : ℂ) (_ : valueAtInfty f = c'),
        Filter.Tendsto f atImInfty (𝓝 c') := fun _ f c' hv ↦ by
      rw [← hv, ← cuspFunction_apply_zero f one_pos one_mem_strictPeriods_SL]
      exact ((analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL
        ).continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
        (fun τ ↦ eq_cuspFunction f τ one_mem_strictPeriods_SL one_ne_zero)
    have h4 := htend _ E4 _ hv4
    have h6 := htend _ E6 _ hv6
    convert ((h4.mul (h4.mul h4)).sub (h6.mul h6)).limUnder_eq using 1
    norm_num)
  obtain ⟨g, hg⟩ := hF_cusp
  obtain ⟨c, hc⟩ := cuspForm_twelve_smul_discriminant g
  have hc_eq : c = 1728 := by
    have hmcast : ∀ {a b : ℤ} (h : a = b) (f : ModularForm 𝒮ℒ a),
        qExpansion 1 (ModularForm.mcast h f : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) :=
      fun _ _ ↦ rfl
    have hgF : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (F : ℍ → ℂ) := by
      congr 1; exact congr_arg DFunLike.coe hg
    have hgΔ : qExpansion 1 (g : ℍ → ℂ) =
        c • qExpansion 1 (discriminantCuspForm : ℍ → ℂ) := by
      conv_lhs => rw [show (g : ℍ → ℂ) = ((c • discriminantCuspForm : CuspForm 𝒮ℒ 12) : ℍ → ℂ)
        from congr_arg DFunLike.coe hc.symm]
      exact qExpansion_smul one_pos one_mem_strictPeriods_SL c discriminantCuspForm
    have h := congr_arg (·.coeff 1) (hgF.symm.trans hgΔ)
    simp only [PowerSeries.coeff_smul, smul_eq_mul, discriminant_qExpansion_coeff_one,
      mul_one] at h
    have hsub := (qExpansionAddHom one_pos one_mem_strictPeriods_SL (k := (12 : ℤ))).map_sub
      (ModularForm.mcast (by norm_num) (E4.mul (ModularForm.mcast rfl (E4.mul E4))))
      (ModularForm.mcast (by norm_num) (E6.mul E6))
    simp only [qExpansionAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hmcast] at hsub
    rw [hsub, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E4
      (ModularForm.mcast rfl (E4.mul E4))] at h
    simp only [hmcast] at h
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E4 E4,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL E6 E6] at h
    have h1_4 : (PowerSeries.coeff 1) (qExpansion 1 E4) = 240 := E_qExpansion_coeff_one_four
    have h1_6 : (PowerSeries.coeff 1) (qExpansion 1 E6) = -504 := E_qExpansion_coeff_one_six
    simp only [map_sub, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.sum_cons, Finset.sum_singleton,
      Finset.map_singleton, Function.Embedding.prodMap, Prod.map,
      Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, Nat.zero_add,
      Function.Embedding.refl_apply, h1_4, h1_6] at h
    exact h.symm.trans (by norm_num [show (PowerSeries.coeff 0) (qExpansion 1 (E4 : ℍ → ℂ)) = 1
      from h0_4, show (PowerSeries.coeff 0) (qExpansion 1 (E6 : ℍ → ℂ)) = 1 from h0_6])
  have h1728 : (1728 : ℂ) * discriminant z = E4 z ^ 3 - E6 z ^ 2 :=
    calc (1728 : ℂ) * discriminant z
        = c * discriminant z := by rw [hc_eq]
      _ = (c • discriminantCuspForm) z := rfl
      _ = g z := by rw [← hc]
      _ = F z := congr_fun (congr_arg DFunLike.coe hg) z
      _ = E4 z ^ 3 - E6 z ^ 2 := hF z
  linear_combination (norm := ring_nf) (1 / 1728 : ℂ) * h1728

private lemma weight_two_eq_zero_of_not_cuspForm (f : ModularForm 𝒮ℒ (2 : ℤ))
    (hf : ¬IsCuspForm f) : f = 0 := by
  exfalso
  obtain ⟨c4, hc4⟩ := exists_smul_eq_of_rank_one weight_four_rank_one
    (E_ne_zero (show 3 ≤ 4 by norm_num) ⟨2, rfl⟩) (f.mul f)
  obtain ⟨c6, hc6⟩ := exists_smul_eq_of_rank_one weight_six_rank_one
    (E_ne_zero (show 3 ≤ 6 by norm_num) ⟨3, rfl⟩) ((f.mul f).mul f)
  set p := qExpansion 1 f
  set p4 := qExpansion 1 (E (show 3 ≤ 4 by norm_num))
  set p6 := qExpansion 1 (E (show 3 ≤ 6 by norm_num))
  have hqc4 : c4 • p4 = p * p := by
    have hsmul := qExpansion_smul one_pos one_mem_strictPeriods_SL c4
      (E (show 3 ≤ 4 by norm_num))
    rw [show (c4 • E (show 3 ≤ 4 by norm_num) : ℍ → ℂ) =
        (f.mul f : ℍ → ℂ) from congrArg DFunLike.coe hc4] at hsmul
    rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f]; exact hsmul.symm
  have hqc6 : c6 • p6 = p * p * p := by
    have hsmul := qExpansion_smul one_pos one_mem_strictPeriods_SL c6
      (E (show 3 ≤ 6 by norm_num))
    have hmul1 := ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (f.mul f) f
    rw [show (c6 • E (show 3 ≤ 6 by norm_num) : ℍ → ℂ) =
        ((f.mul f).mul f : ℍ → ℂ) from congrArg DFunLike.coe hc6] at hsmul
    rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f] at hmul1
    rw [← hmul1]; exact hsmul.symm
  have hp4_0 : p4.coeff 0 = 1 :=
    E_qExpansion_coeff_zero (show 3 ≤ 4 by norm_num) ⟨2, rfl⟩
  have hp6_0 : p6.coeff 0 = 1 :=
    E_qExpansion_coeff_zero (show 3 ≤ 6 by norm_num) ⟨3, rfl⟩
  have h0_4 : c4 = p.coeff 0 ^ 2 := by
    have h := congr_arg (·.coeff 0) hqc4
    simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hp4_0, mul_one] at h
    rw [sq]; exact h
  have h0_6 : c6 = p.coeff 0 ^ 3 := by
    have h := congr_arg (·.coeff 0) hqc6
    simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hp6_0, mul_one] at h
    rw [show p.coeff 0 ^ 3 = p.coeff 0 * p.coeff 0 * p.coeff 0 by ring]; exact h
  have hp4_1 : p4.coeff 1 = 240 := E_qExpansion_coeff_one_four
  have hp6_1 : p6.coeff 1 = -504 := E_qExpansion_coeff_one_six
  have heq4 : p.coeff 0 ^ 2 * 240 = 2 * p.coeff 0 * p.coeff 1 := by
    have h := congr_arg (·.coeff 1) hqc4
    simp only [PowerSeries.coeff_smul, smul_eq_mul, hp4_1] at h
    rw [show (p * p).coeff 1 = 2 * p.coeff 0 * p.coeff 1 from by
      simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]; ring, h0_4] at h
    exact h
  have heq6 : p.coeff 0 ^ 3 * (-504) = 3 * p.coeff 0 ^ 2 * p.coeff 1 := by
    have h := congr_arg (·.coeff 1) hqc6
    simp only [PowerSeries.coeff_smul, smul_eq_mul, hp6_1] at h
    rw [show (p * p * p).coeff 1 = 3 * p.coeff 0 ^ 2 * p.coeff 1 from by
      simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]; ring, h0_6] at h
    exact h
  refine hf ((isCuspForm_iff_coeffZero_eq_zero f).mpr <|
    pow_eq_zero_iff (n := 3) three_ne_zero |>.mp ?_)
  have h0 : (1728 : ℂ) * p.coeff 0 ^ 3 = 0 := by
    linear_combination 3 * p.coeff 0 * heq4 - 2 * heq6
  exact (mul_eq_zero.mp h0).resolve_left (by norm_num)

/-- Modular forms of weight 2 for `𝒮ℒ` are zero. -/
theorem ModularForm.levelOne_weight_two_rank_zero :
    Module.rank ℂ (ModularForm 𝒮ℒ (2 : ℤ)) = 0 := by
  rw [rank_zero_iff_forall_zero]
  intro f
  by_cases hf : IsCuspForm f
  · obtain ⟨g, hg⟩ := hf
    rw [← hg]
    simp [rank_zero_iff_forall_zero.mp
      (cuspForm_rank_lt_twelve (show (2 : ℤ) < 12 by norm_num)) g]
  · exact weight_two_eq_zero_of_not_cuspForm f hf

private lemma floor_lem1 (k a : ℚ) (ha : 0 < a) (hak : a ≤ k) :
    1 + Nat.floor ((k - a) / a) = Nat.floor (k / a) := by
  rw [div_sub_same (Ne.symm (ne_of_lt ha))]
  have := Nat.floor_sub_one (k / a)
  push_cast at *
  rw [this]
  refine Nat.add_sub_cancel' ?_
  exact Nat.le_floor ((le_div_iff₀ ha).mpr (by simpa using hak))

/-- The dimension formula for `𝒮ℒ` modular forms of even weight `k ≥ 3`. -/
theorem ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ (k : ℤ)) =
    if 12 ∣ ((k : ℤ) - 2) then Nat.floor ((k : ℚ) / 12)
    else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  rw [rank_eq_one_add_rank_cuspForm (by omega) hk2,
    LinearEquiv.rank_eq CuspForm.discriminantEquiv]
  by_cases HK : (3 : ℤ) ≤ ((k : ℤ) - 12)
  · have iH := ihn (k - 12) (by omega) (by omega)
      ((Nat.even_sub (by omega)).mpr (by simp only [hk2, true_iff]; decide))
    have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by
      norm_cast; exact Eq.symm (Int.subNatNat_of_le (by omega))
    rw [hk12] at iH
    rw [iH, show ((k - 12 : ℕ) : ℚ) = (k : ℚ) - 12 from by norm_cast]
    have hfl := floor_lem1 k 12 (by norm_num)
    by_cases h12 : 12 ∣ ((k) : ℤ) - 2
    · simp only [show 12 ∣ (k : ℤ) - 12 - 2 from by omega, ↓reduceIte, h12]
      norm_cast at *; apply hfl; omega
    · simp only [show ¬ 12 ∣ (k : ℤ) - 12 - 2 from by omega, ↓reduceIte, h12,
        Nat.cast_add, Nat.cast_one]
      norm_cast at *; rw [← add_assoc, hfl]; omega
  · simp only [not_le] at HK
    have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
      simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]; omega
    rw [show Finset.filter Even (Finset.Icc 3 14) = ({4, 6, 8, 10, 12, 14} : Finset ℕ)
      from by decide] at hkop
    fin_cases hkop <;> simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg] at *
    all_goals first
      | exact (congrArg (1 + ·) (levelOne_neg_weight_rank_zero (by omega))).trans (by norm_cast)
      | exact (congrArg (1 + ·) levelOne_weight_zero_rank_one).trans (by norm_cast)
      | exact (congrArg (1 + ·) levelOne_weight_two_rank_zero).trans (by norm_cast)

end DimensionFormula

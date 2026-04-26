/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Dimension formula for level 1 modular forms

This file proves the dimension formula for the space of modular forms for `𝒮ℒ` (= `SL(2, ℤ)`)
of even weight `k ≥ 3`.

## Main results

* `CuspForm.discriminantEquiv`: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.
* `ModularForm.rank_eq_one_add_rank_cuspForm`: `rank M_k = 1 + rank S_k` for even `k ≥ 3`.
* `ModularForm.dimension_level_one`: the full dimension formula.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm Complex SlashInvariantForm SlashInvariantFormClass
  ModularFormClass CuspFormClass CongruenceSubgroup MatrixGroups OnePoint Filter Topology
  EisensteinSeries Asymptotics

/-! ### Delta isomorphism: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)` -/

section DeltaIsomorphism

variable {k : ℤ}

local notation "Δ" => ModularForm.discriminant

namespace CuspForm

/-- Multiply a modular form of weight `k - 12` by the discriminant to get a cusp form of
weight `k`. Built directly as a `CuspForm` (no `IsCuspForm` intermediary). -/
def ofMulDiscriminant (f : ModularForm 𝒮ℒ (k - 12)) : CuspForm 𝒮ℒ k := by
  let Δ' : ModularForm 𝒮ℒ 12 := discriminantCuspForm
  apply ModularForm.toCuspForm (ModularForm.mcast (by ring) (f.mul Δ'))
  rw [show (ModularForm.mcast _ (f.mul Δ')) = (⇑f : ℍ → ℂ) * Δ' from rfl,
    qExpansion_mul_coeff_zero
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
        one_mem_strictPeriods_SL).continuousAt
      (ModularFormClass.analyticAt_cuspFunction_zero Δ' one_pos
        one_mem_strictPeriods_SL).continuousAt,
    (isCuspForm_iff_coeffZero_eq_zero Δ').mp ⟨discriminantCuspForm, rfl⟩, mul_zero]

@[simp]
lemma ofMulDiscriminant_apply (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ) :
    (ofMulDiscriminant f) z = f z * Δ z := rfl

private lemma divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (fun z ↦ f z / Δ z) ∣[k - 12] γ = fun z ↦ f z / Δ z := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hf z := (ModularGroup.sl_moeb γ z).symm ▸ slash_action_eqn'' f hγ z
  have hΔ z := (ModularGroup.sl_moeb γ z).symm ▸ slash_action_eqn'' discriminantCuspForm hγ z
  ext z; rw [SL_slash_apply, hf, show Δ (γ • z) = denom γ z ^ (12 : ℤ) * Δ z from hΔ z,
    div_mul_eq_mul_div, mul_right_comm, ← zpow_add₀ (denom_ne_zero γ z),
    show k + -(k - 12) = (12 : ℤ) by ring]
  exact mul_div_mul_left (f z) (Δ z) (zpow_ne_zero _ (denom_ne_zero γ z))

lemma exp_decay_isBigO_discriminant (f : CuspForm 𝒮ℒ k) : f =O[atImInfty] Δ := by
  have hf_decay := exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL
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
    linarith [norm_nonneg (Function.Periodic.qParam 1 (τ : ℂ)), mul_le_mul_of_nonneg_left
      hprod_bound (norm_nonneg (Function.Periodic.qParam 1 (τ : ℂ)))]
  exact hf_decay.trans (IsBigO.of_bound 2 hΔ_lower)

/-- Divide a cusp form by the discriminant to get a modular form of weight `k - 12`. -/
def divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) where
  toFun z := f z / Δ z
  slash_action_eq' _ hA := by obtain ⟨γ, rfl⟩ := hA; exact divByDiscriminant_slash_eq f γ
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    exact (UpperHalfPlane.mdifferentiable_iff.mp f.holo').div
      (UpperHalfPlane.mdifferentiable_iff.mp discriminantCuspForm.holo') fun z hz ↦ by
        simpa [ofComplex_apply_of_im_pos hz] using discriminant_ne_zero ⟨z, hz⟩
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc; rw [isBoundedAt_iff_forall_SL2Z hc]
    intro γ _; rw [divByDiscriminant_slash_eq f γ, IsBoundedAtImInfty, BoundedAtFilter]
    exact (div_isBoundedUnder_of_isBigO (exp_decay_isBigO_discriminant f)).isBigO_one ℝ

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
  left_inv f := by ext z; exact div_mul_cancel₀ (f z) (discriminant_ne_zero z)
  right_inv f := by ext z; exact mul_div_cancel_right₀ (f z) (discriminant_ne_zero z)

end CuspForm

end DeltaIsomorphism

/-! ### Rank identities -/

section RankIdentity

variable {k : ℤ}

/-- Cusp forms of weight `k < 12` for `𝒮ℒ` are zero-dimensional. -/
lemma cuspForm_rank_lt_twelve (hk : k < 12) : Module.rank ℂ (CuspForm 𝒮ℒ k) = 0 :=
  (LinearEquiv.rank_eq CuspForm.discriminantEquiv).trans
    (levelOne_neg_weight_rank_zero (by omega))

/-- The space of weight 12 cusp forms for `𝒮ℒ` has rank 1. -/
lemma cuspForm_rank_twelve : Module.rank ℂ (CuspForm 𝒮ℒ 12) = 1 := by
  rw [LinearEquiv.rank_eq CuspForm.discriminantEquiv, show (12 : ℤ) - 12 = 0 by decide]
  exact levelOne_weight_zero_rank_one

/-- Every weight 12 cusp form for `𝒮ℒ` is a scalar multiple of the discriminant. -/
lemma cuspForm_twelve_smul_discriminant (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • discriminantCuspForm = f :=
  (finrank_eq_one_iff_of_nonzero' discriminantCuspForm (fun h ↦
      discriminant_ne_zero UpperHalfPlane.I (DFunLike.congr_fun h _))).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp cuspForm_rank_twelve) f

/-- For even `k ≥ 3`, the rank of `𝒮ℒ` modular forms is one more than the rank of
cusp forms. -/
lemma ModularForm.rank_eq_one_add_rank_cuspForm {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) = 1 + Module.rank ℂ (CuspForm 𝒮ℒ k) := by
  have h_add := Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ k)
  rw [← LinearEquiv.rank_eq (CuspForm.equivCuspFormSubmodule 𝒮ℒ k)] at h_add
  suffices h1 : Module.rank ℂ (ModularForm 𝒮ℒ k ⧸ cuspFormSubmodule 𝒮ℒ k) = 1 by
    rw [← h_add, h1]
  have hE := E_qExpansion_coeff_zero hk hk2
  apply rank_eq_one (Submodule.Quotient.mk (p := cuspFormSubmodule 𝒮ℒ k) (E hk))
  · intro h
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact one_ne_zero <| hE.symm.trans <| (isCuspForm_iff_coeffZero_eq_zero _).mp h
  · refine (Submodule.Quotient.mk_surjective _).forall.mpr fun f ↦
      ⟨(qExpansion 1 f).coeff 0, ?_⟩
    have h_mem : f - (qExpansion 1 ↑f).coeff 0 • E hk ∈ cuspFormSubmodule 𝒮ℒ k := by
      apply (isCuspForm_iff_coeffZero_eq_zero _).mpr
      set c := (qExpansion 1 ↑f).coeff 0 with hc
      have hsub := (qExpansionAddHom one_pos one_mem_strictPeriods_SL (k := k)).map_sub f
        (c • E hk)
      simp only [qExpansionAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hsub
      rw [hsub, show qExpansion 1 ⇑(c • E hk) = c • qExpansion 1 ⇑(E hk) from
        qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero (E hk) one_pos
          one_mem_strictPeriods_SL) c,
        _root_.map_sub, _root_.map_smul, smul_eq_mul, hE, mul_one, ← hc, sub_self]
    have h0 : (cuspFormSubmodule 𝒮ℒ k).mkQ (f - (qExpansion 1 ↑f).coeff 0 • E hk) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr h_mem
    rwa [map_sub, LinearMap.map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
      sub_eq_zero, eq_comm] at h0

end RankIdentity

/-! ### Dimension formula -/

section DimensionFormula

private lemma weight_four_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 4) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (cuspForm_rank_lt_twelve (by norm_num))).trans (by norm_cast))

private lemma weight_six_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 6) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (cuspForm_rank_lt_twelve (by norm_num))).trans (by norm_cast))

private lemma E₄_qExpansion_coeff_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli (4 : ℕ) = ((-1 : ℚ) / 30 : ℚ) by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]; exact bernoulli'_four]
  simp [ArithmeticFunction.sigma_one]; norm_num

private lemma E₆_qExpansion_coeff_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli (6 : ℕ) = ((1 : ℚ) / 42 : ℚ) by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero,
      show Nat.choose 6 2 = 15 by decide, show Nat.choose 6 4 = 15 by decide,
      bernoulli'_eq_zero_of_odd (show Odd 5 from ⟨2, rfl⟩) (by norm_num)]]
  simp [ArithmeticFunction.sigma_one]; norm_num

/- Algebraic core of the weight-2 vanishing argument: if `p : PowerSeries ℂ`
satisfies `c₄ • p₄ = p²` and `c₆ • p₆ = p³` for power series `p₄`, `p₆` with
constant term `1` and first-order coefficients `240` and `-504`, then `p.coeff 0 = 0`. -/
private lemma coeffZero_eq_zero_of_pow_eq_smul {p p4 p6 : PowerSeries ℂ} {c4 c6 : ℂ}
    (hp4_0 : p4.coeff 0 = 1) (hp6_0 : p6.coeff 0 = 1) (hp4_1 : p4.coeff 1 = 240)
    (hp6_1 : p6.coeff 1 = -504) (hqc4 : c4 • p4 = p * p)
    (hqc6 : c6 • p6 = p * p * p) : p.coeff 0 = 0 := by
  have h40 := congr_arg (·.coeff 0) hqc4
  have h41 := congr_arg (·.coeff 1) hqc4
  have h60 := congr_arg (·.coeff 0) hqc6
  have h61 := congr_arg (·.coeff 1) hqc6
  simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_zero, Finset.Nat.antidiagonal_succ, Finset.sum_singleton,
    Finset.sum_cons, Finset.map_singleton, Function.Embedding.prodMap, Prod.map,
    Function.Embedding.coeFn_mk, Function.Embedding.refl_apply, hp4_0, hp4_1, hp6_0, hp6_1,
    mul_one] at h40 h41 h60 h61
  refine pow_eq_zero_iff (n := 3) three_ne_zero |>.mp ?_
  have h0 : (1728 : ℂ) * p.coeff 0 ^ 3 = 0 := by
    linear_combination 3 * p.coeff 0 * h41 - 2 * h61 - 720 * p.coeff 0 * h40 - 1008 * h60
  exact (mul_eq_zero.mp h0).resolve_left (by norm_num)

private lemma weight_two_eq_zero_of_not_cuspForm (f : ModularForm 𝒮ℒ 2) (hf : ¬IsCuspForm f) :
    f = 0 := by
  exfalso
  obtain ⟨c4, hc4⟩ := (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp weight_four_rank_one) (f.mul f)
  obtain ⟨c6, hc6⟩ := (finrank_eq_one_iff_of_nonzero' E₆ (E_ne_zero _ ⟨3, rfl⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp weight_six_rank_one) ((f.mul f).mul f)
  have hqc4 : c4 • qExpansion 1 (E₄ : ℍ → ℂ) =
      qExpansion 1 (f : ℍ → ℂ) * qExpansion 1 f := by
    rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f,
      ← ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c4 E₄,
      show (c4 • E₄ : ℍ → ℂ) = (f.mul f) from congrArg DFunLike.coe hc4]
  have hqc6 : c6 • qExpansion 1 E₆ = qExpansion 1 f * qExpansion 1 f * qExpansion 1 f := by
    rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f,
      ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (f.mul f) f,
      ← ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c6 E₆,
      show (c6 • E₆ : ℍ → ℂ) = (f.mul f).mul f from congrArg DFunLike.coe hc6]
  exact hf <| (isCuspForm_iff_coeffZero_eq_zero f).mpr <|
    coeffZero_eq_zero_of_pow_eq_smul (E_qExpansion_coeff_zero _ ⟨2, rfl⟩)
      (E_qExpansion_coeff_zero _ ⟨3, rfl⟩) E₄_qExpansion_coeff_one E₆_qExpansion_coeff_one
      hqc4 hqc6

/-- Modular forms of weight 2 for `𝒮ℒ` are zero. -/
theorem ModularForm.levelOne_weight_two_rank_zero :
    Module.rank ℂ (ModularForm 𝒮ℒ 2) = 0 := by
  rw [rank_zero_iff_forall_zero]; intro f
  by_cases hf : IsCuspForm f
  · obtain ⟨g, hg⟩ := hf; rw [← hg]
    simp [rank_zero_iff_forall_zero.mp (cuspForm_rank_lt_twelve (by norm_num)) g]
  · exact weight_two_eq_zero_of_not_cuspForm f hf

/-- The dimension formula for `𝒮ℒ` modular forms of even weight `k ≥ 3`. -/
theorem ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) =
      if 12 ∣ ((k : ℤ) - 2) then Nat.floor ((k : ℚ) / 12)
      else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  rw [rank_eq_one_add_rank_cuspForm (by omega) hk2,
    LinearEquiv.rank_eq CuspForm.discriminantEquiv]
  by_cases HK : (3 : ℤ) ≤ (k : ℤ) - 12
  · have iH := ihn (k - 12) (by omega) (by omega)
      ((Nat.even_sub (by omega)).mpr (by simp only [hk2, true_iff]; decide))
    have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by grind
    rw [hk12] at iH
    rw [iH, show ((k - 12 : ℕ) : ℚ) = (k : ℚ) - 12 by norm_cast]
    have hfl (hk' : (12 : ℚ) ≤ k) :
        ⌊(k : ℚ) / 12⌋₊ = 1 + ⌊((k : ℚ) - 12) / 12⌋₊ :=
      Nat.floor_div_eq_one_add_floor_sub_div (k : ℚ) 12 (by norm_num) hk'
    by_cases h12 : 12 ∣ (k : ℤ) - 2
    · simp only [show 12 ∣ (k : ℤ) - 12 - 2 by omega, ↓reduceIte, h12]; norm_cast at *
      rw [hfl (by exact_mod_cast (by omega : (12 : ℤ) ≤ k))]
    · simp only [show ¬ 12 ∣ (k : ℤ) - 12 - 2 by omega, ↓reduceIte, h12,
        Nat.cast_add, Nat.cast_one]; norm_cast at *
      rw [← add_assoc, ← hfl (by exact_mod_cast (by omega : (12 : ℤ) ≤ k))]
  · simp only [not_le] at HK
    have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
      simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]; omega
    rw [show Finset.filter Even (Finset.Icc 3 14) = ({4, 6, 8, 10, 12, 14} : Finset ℕ) by
      decide] at hkop
    fin_cases hkop <;> simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg] at *
    all_goals first
      | exact (congrArg (1 + ·) (levelOne_neg_weight_rank_zero (by omega))).trans (by norm_cast)
      | exact (congrArg (1 + ·) levelOne_weight_zero_rank_one).trans (by norm_cast)
      | exact (congrArg (1 + ·) levelOne_weight_two_rank_zero).trans (by norm_cast)

end DimensionFormula

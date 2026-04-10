/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.Analysis.PSeries

/-!
# The `L`-function of a modular form
-/

@[expose] public section

open UpperHalfPlane hiding I
open scoped Real
open Filter Complex MatrixGroups Asymptotics

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
  {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ]

lemma tendsto_ofComplex_I_mul_atTop_atImInfty :
    Tendsto (fun t : ℝ ↦ ofComplex (I * t)) atTop atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← UpperHalfPlane.coe_im]

lemma continuousOn_ofComplex_I_mul :
    ContinuousOn (fun t : ℝ ↦ ofComplex (I * ↑t)) (Set.Ioi 0) := by
  have : Continuous (fun t : ℝ ↦ I * ↑t) := by fun_prop
  simp only [ofComplex_apply_eq_ite, I_mul_im, ofReal_re,
    continuousOn_iff_continuous_restrict, continuous_induced_rng]
  exact (this.comp continuous_subtype_val).congr (by simp +contextual)

namespace ModularForm

variable [ModularFormClass F 𝒮ℒ k]

/-- A `WeakFEPair` structure associated to a level 1 modular form. -/
noncomputable def weakFEPair (f : F) : WeakFEPair ℂ where
  f t := f (ofComplex (I * t))
  g t := f (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty f
  hf_int := by
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    exact (show Continuous f by fun_prop).comp_continuousOn continuousOn_ofComplex_I_mul
  hg_int := by
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
    exact (show Continuous f by fun_prop).comp_continuousOn continuousOn_ofComplex_I_mul
  h_feq t (ht : 0 < t) := by
    have : ↑ModularGroup.S ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
    convert SlashInvariantForm.slash_action_eqn' f this ⟨I * t, by simpa using ht⟩
    · ext
      rw [coe_smul_of_det_pos (by simp), ofComplex_apply_of_im_pos (by simpa using ht)]
      simp [ModularGroup.S, num, denom, div_eq_mul_inv, mul_comm]
    · simp [mul_zpow, ModularGroup.S]
    · simp [ht, ofComplex_apply_eq_ite]
  hf_top r := by
    obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
    refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
    refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [ht, ofComplex_apply_of_im_pos, ← coe_im]
  hg_top r := by
    obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
    refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
    refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [ht, ofComplex_apply_of_im_pos, ← coe_im]

/-- The `L`-series of a modular form (including its Archimedean `Γ`-factor). -/
noncomputable def Λ (f : F) : ℂ → ℂ := (weakFEPair hk f).Λ

lemma hasSum_Λ (f : F) {s : ℂ} (hk : 0 < k) (hs : k + 1 < s.re) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s *
      (ModularFormClass.qExpansion 1 f).coeff n / ↑(2 * n : ℝ) ^ s) (Λ hk f s) := by
  have hk' : 0 < (k : ℝ) := mod_cast hk
  have : (weakFEPair hk f).k < s.re := by simp only [weakFEPair]; linarith
  have := ((weakFEPair hk f).hasMellin this).2
  rw [Λ, ← this]
  refine hasSum_mellin_pi_mul₀ (fun _ ↦ by positivity) (by linarith) ?_ ?_
  · intro t (ht : 0 < t)
    have hh : 0 < (1 : ℝ) := zero_lt_one
    have hΓ : 1 ∈ Subgroup.strictPeriods 𝒮ℒ := by simp [Subgroup.strictPeriods_SL2Z]
    have := ModularFormClass.hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have := I_sq
        simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
        grind
    · simp [ModularFormClass.qExpansion_coeff_zero f hh hΓ, weakFEPair]
  · simp_rw [Real.mul_rpow two_pos.le (Nat.cast_nonneg _), mul_comm, ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show k - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show k - s.re ≠ 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa [Subgroup.strictWidthInfty_SL2Z] using (ModularFormClass.qExpansion_isBigO hk.le f)

/-- The `L`-series of a modular form (without its Archimedean `Γ`-factor). -/
noncomputable def L (f : F) (s : ℂ) : ℂ :=  Λ hk f s * (2 / Gammaℂ s)

end ModularForm

open ModularForm

namespace CuspForm

variable [CuspFormClass F 𝒮ℒ k]

/-- A `StrongFEPair` structure associated to a level 1 cusp form. -/
noncomputable def strongFEPair (f : F) : StrongFEPair ℂ where
  __ := ModularForm.weakFEPair hk f
  hf₀ := (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero

lemma differentiable_Λ (f : F) : Differentiable ℂ (Λ hk f) :=
  (strongFEPair hk f).differentiable_Λ

lemma Λ_eq_mellin (f : F) : Λ hk f = mellin (fun t ↦ f (ofComplex (I * t))) :=
  (strongFEPair hk f).Λ_eq

lemma hasSum_Λ (f : F) {s : ℂ} (hk : 0 < k) (hs : k / 2 + 1 < s.re) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s *
      (ModularFormClass.qExpansion 1 f).coeff n / ↑(2 * n : ℝ) ^ s) (Λ hk f s) := by
  rw [Λ_eq_mellin]
  refine hasSum_mellin_pi_mul ?_ (by linarith [show (0 : ℝ) < k from mod_cast hk]) ?_ ?_
  · intro i
    rcases eq_or_ne i 0 with rfl | hi
    · simp [ModularFormClass.qExpansion_coeff_zero,
        (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]
    · right
      positivity
  · intro t (ht : 0 < t)
    convert ModularFormClass.hasSum_qExpansion f one_pos ?_ (ofComplex (I * t)) with n
    · rw [Function.Periodic.qParam, Complex.ofReal_exp, ← exp_nat_mul]
      congr 1
      simp only [neg_mul, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_natCast,
        ofComplex_apply_eq_ite, mul_im, Complex.I_re, ofReal_im, mul_zero, Complex.I_im, ofReal_re,
        one_mul, zero_add, ht, ↓reduceDIte, coe_mk, ofReal_one]
      grind [I_sq]
    · simpa only [Subgroup.strictPeriods_SL2Z] using AddSubgroup.mem_zmultiples 1
  · simp_rw [Real.mul_rpow two_pos.le (Nat.cast_nonneg _), mul_comm, ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show k/2 - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show k/2 - s.re ≠ 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa [Subgroup.strictWidthInfty_SL2Z] using CuspFormClass.qExpansion_isBigO f

lemma differentiable_L (f : F) : Differentiable ℂ (L hk f) := by
  refine (differentiable_Λ hk f).mul ?_
  apply (differentiable_const _).mul ?_
  simp only [Gammaℂ_def, mul_inv]
  refine ((differentiable_const _).mul ?_).mul differentiable_one_div_Gamma
  simpa only [cpow_neg, inv_inv] using differentiable_id.const_cpow (by simp)

theorem hasSum_L (f : F) {s : ℂ} (hk : 0 < k) (hs : k / 2 + 1 < s.re) :
    HasSum (fun i ↦ (ModularFormClass.qExpansion 1 f).coeff i / ↑i ^ s) (L hk f s) := by
  convert (CuspForm.hasSum_Λ f hk hs).mul_right (2 / Gammaℂ s) using 1
  ext n
  rw [Gammaℂ, ← ofReal_ofNat, ofReal_mul, mul_cpow_ofReal_nonneg two_pos.le (Nat.cast_nonneg _),
    mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le, cpow_neg (2 : ℝ), ofReal_natCast]
  field_simp [Gamma_ne_zero_of_re_pos
    (show 0 < s.re by linarith [show (0 : ℝ) < k from mod_cast hk])]

end CuspForm

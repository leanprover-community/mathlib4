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
  {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ] (f : F) {s : ℂ}

local notation "h" => Subgroup.strictWidthInfty

open ConjAct Pointwise in
private local instance :
    Subgroup.IsArithmetic (toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹ • Γ) := by
  convert Subgroup.IsArithmetic.conj Γ ↑(ModularGroup.S⁻¹)
  simp only [ModularGroup.S_inv, ← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

namespace ModularForm

variable [ModularFormClass F Γ k]

section asymptotics -- private lemmas about aymptotics along `I * ℝ`

private lemma tendsto_ofComplex_I_mul_atTop_atImInfty :
    Tendsto (fun t : ℝ ↦ ofComplex (I * t)) atTop atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

include F k Γ in -- conclusion doesn't explicitly refer these
private lemma isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (r : ℝ) :
    (fun t : ℝ ↦ f (ofComplex (I * t)) - valueAtInfty f) =O[atTop] (fun t ↦ t ^ r) := by
  obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
  refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos, ← coe_im]

end asymptotics

/-- A `WeakFEPair` structure associated to a modular form. -/
@[simps] noncomputable def weakFEPair : WeakFEPair ℂ where
  f t := f (ofComplex (I * t))
  g t := translate f ModularGroup.S (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty (translate f ModularGroup.S)
  hf_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  hg_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  h_feq t (ht : 0 < t) := by
    rw [coe_translate, slash_def]
    suffices f (ofComplex (I * t⁻¹)) = I ^ k * t ^ k *
        (f ((ModularGroup.S : GL (Fin 2) ℝ) • ofComplex (I * t)) * ofComplex (I * t) ^ (-k)) by
      simpa [σ, denom]
    rw [ofComplex_apply_of_im_pos (by simpa), ofComplex_apply_of_im_pos (by simpa),
      mul_comm (f _), ← mul_assoc, ← mul_zpow, zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero _ (by aesop))]
    simp only [one_mul]
    congr 1
    ext
    rw [coe_smul_of_det_pos (by simp)]
    simp [num, denom, div_eq_mul_inv, mul_comm]
  hf_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty f r
  hg_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (translate f ModularGroup.S) r

/-- The `L`-series of a modular form (including its Archimedean `Γ`-factor). -/
noncomputable def Λ : ℂ → ℂ := (weakFEPair hk f).Λ

/-- Shared Dirichlet-series summability argument for modular and cusp forms. -/
private lemma hasSum_Λ_of_qExpansion_isBigO {r : ℝ}
    (hpos : 0 < s.re) (hs : r + 1 < s.re)
    (hΛ : Λ hk f s = mellin (fun t ↦ (weakFEPair hk f).f t - (weakFEPair hk f).f₀) s)
    (hcoeff : (fun n ↦ (qExpansion (h Γ) f).coeff n) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n /
      ↑(2 * n / h Γ : ℝ) ^ s) (Λ hk f s) := by
  rw [hΛ]
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  refine hasSum_mellin_pi_mul₀ (fun _ ↦ by positivity) hpos ?_ ?_
  · -- show `q`-expansion converges to `f` on positive imaginary axis
    intro t (ht : 0 < t)
    have := hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert! hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
        grind [I_sq]
    · simp only [weakFEPair]
      rw [qExpansion_coeff_zero hh, pow_zero, mul_one]
      · exact ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
      · exact SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  · -- show summability of Dirichlet series
    simp_rw [mul_comm (2 : ℝ), mul_div_assoc,
      Real.mul_rpow (Nat.cast_nonneg _) (show 0 ≤ 2 / h Γ by positivity), ← div_div]
    apply Summable.div_const
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr <| show r - s.re < -1 by linarith)
    simp only [Real.rpow_sub' (Nat.cast_nonneg _) (show r - s.re ≠ 0 by linarith)]
    apply IsBigO.mul _ (isBigO_refl _ _)
    simpa using hcoeff.norm_left

lemma hasSum_Λ (hs : k + 1 < s.re) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n /
      ↑(2 * n / h Γ : ℝ) ^ s) (Λ hk f s) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k)
    (by linarith [show (0 : ℝ) < k from mod_cast hk]) (by exact_mod_cast hs) ?_ ?_
  · rw [Λ, ← ((weakFEPair hk f).hasMellin <| by grind [weakFEPair]).2]
  · simpa using ModularFormClass.qExpansion_isBigO hk.le f

/-- The `L`-series of a modular form (without its Archimedean `Γ`-factor). -/
noncomputable def L (s : ℂ) : ℂ :=  Λ hk f s * (2 / Gammaℂ s)

/-- Shared conversion from the completed `Λ`-series to the ordinary `L`-series. -/
private lemma hasSum_L_of_hasSum_Λ (hs : 0 < s.re)
    (hΛ : HasSum (fun n ↦ π ^ (-s) * Gamma s *
      (qExpansion (h Γ) f).coeff n / ↑(2 * n / h Γ : ℝ) ^ s) (Λ hk f s)) :
    HasSum (fun i ↦ (qExpansion (h Γ) f).coeff i / ↑i ^ s) (h Γ ^ (-s) * L hk f s) := by
  convert! hΛ.mul_right (2 / Gammaℂ s * h Γ ^ (-s)) using 1
  · ext n
    generalize (PowerSeries.coeff n) (qExpansion (h Γ) f) = p
    rw [Gammaℂ, ← div_div, ← div_div, div_self two_ne_zero, one_div, cpow_neg (2 * _), inv_inv,
      ← ofReal_ofNat, mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le]
    simp only [ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_natCast]
    have : (2 * n / h Γ : ℂ) ^ s = 2 ^ s * n ^ s / h Γ ^ s := by
      rw [← ofReal_ofNat, ← ofReal_natCast, ← ofReal_mul,
        div_cpow_ofReal_nonneg (by grind) Γ.strictWidthInfty_nonneg, ofReal_mul,
        mul_cpow_ofReal_nonneg zero_le_two n.cast_nonneg]
    rw [this, cpow_neg, cpow_neg]
    have := Gamma_ne_zero_of_re_pos hs
    have := cpow_ne_zero_iff (y := s).mpr (.inl <| ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne')
    field_simp
  · grind [L]

theorem hasSum_L (hs : k + 1 < s.re) :
    HasSum (fun n ↦ (qExpansion (h Γ) f).coeff n / n ^ s) (h Γ ^ (-s) * L hk f s) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : ℝ) < k from mod_cast hk]) (hasSum_Λ hk f hs)

end ModularForm

open ModularForm

namespace CuspForm

variable [CuspFormClass F Γ k]

/-- For cusp forms the FE-pair is a strong FE-pair. -/
lemma isStrongFEPair : IsStrongFEPair (weakFEPair hk f) where
  hf₀ := (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty <| translate f ModularGroup.S).valueAtInfty_eq_zero

@[fun_prop]
lemma differentiable_Λ : Differentiable ℂ (Λ hk f) :=
  (isStrongFEPair hk f).differentiable_Λ

lemma Λ_eq_mellin : Λ hk f = mellin (fun t ↦ f (ofComplex (I * t))) :=
  (isStrongFEPair hk f).Λ_eq

lemma hasSum_Λ (hk : 0 < k) (hs : k / 2 + 1 < s.re) :
    HasSum (fun n ↦ π ^ (-s) * Gamma s * (qExpansion (h Γ) f).coeff n / ↑(2 * n / h Γ : ℝ) ^ s)
      (Λ hk f s) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k / 2)
    (by linarith [show (0 : ℝ) < k from mod_cast hk]) hs ?_ ?_
  · simp [Λ_eq_mellin, (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]
  · simpa using CuspFormClass.qExpansion_isBigO f

@[fun_prop]
lemma differentiable_L : Differentiable ℂ (L hk f) := by
  unfold L
  simp only [div_eq_mul_inv]
  fun_prop

theorem hasSum_L (hs : k / 2 + 1 < s.re) :
    HasSum (fun n ↦ (qExpansion (h Γ) f).coeff n / n ^ s) (h Γ ^ (-s) * L hk f s) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : ℝ) < k from mod_cast hk]) (hasSum_Λ f hk hs)

end CuspForm

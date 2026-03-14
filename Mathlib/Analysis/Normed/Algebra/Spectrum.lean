/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Real.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Topology.Algebra.Module.CharacterSpace
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.
Theorems specific to *complex* Banach algebras, such as *Gelfand's formula* can be found in
 `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`.

## Main definitions

* `spectralRadius : ℝ≥0∞`: supremum of `‖k‖₊` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `spectrum.isOpen_resolventSet`: the resolvent set is open.
* `spectrum.isClosed`: the spectrum is closed.
* `spectrum.subset_closedBall_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.isCompact`: the spectrum is compact.
* `spectrum.spectralRadius_le_nnnorm`: the spectral radius is bounded above by the norm.

-/

@[expose] public section

assert_not_exists ProbabilityTheory.cond
assert_not_exists HasFDerivAt

open NormedSpace Topology -- For `NormedSpace.exp`.
open scoped ENNReal NNReal

/-- The *spectral radius* is the supremum of the `nnnorm` (`‖·‖₊`) of elements in the spectrum,
coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
case, `spectralRadius a = 0`. It is also possible that `spectrum 𝕜 a` be unbounded (though
not for Banach algebras, see `spectrum.isBounded`, below).  In this case,
`spectralRadius a = ∞`. -/
noncomputable def spectralRadius (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ spectrum 𝕜 a, ‖k‖₊

variable {𝕜 : Type*} {A : Type*}

namespace spectrum

section SpectrumCompact

open Filter

variable [NormedField 𝕜]

local notation "σ" => spectrum 𝕜
local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

section Algebra

variable [Ring A] [Algebra 𝕜 A]

@[simp]
theorem SpectralRadius.of_subsingleton [Subsingleton A] (a : A) :
    spectralRadius 𝕜 a = 0 := by
  simp [spectralRadius]

@[simp]
theorem spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0 := by
  nontriviality A
  simp [spectralRadius]

@[simp]
theorem spectralRadius_one [Nontrivial A] :
    spectralRadius 𝕜 (1 : A) = 1 := by
  simp [spectralRadius]

theorem mem_resolventSet_of_spectralRadius_lt {a : A} {k : 𝕜}
    (h : spectralRadius 𝕜 a < ‖k‖₊) : k ∈ ρ a :=
  Classical.not_not.mp fun hn => h.not_ge <| le_iSup₂ (α := ℝ≥0∞) k hn

lemma spectralRadius_pow_le (a : A) (n : ℕ) (hn : n ≠ 0) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  simp only [spectralRadius, ENNReal.iSup₂_pow_of_ne_zero _ hn]
  refine iSup₂_le fun x hx ↦ ?_
  apply le_iSup₂_of_le (x ^ n) (spectrum.pow_mem_pow a n hx)
  simp

lemma spectralRadius_pow_le' [Nontrivial A] (a : A) (n : ℕ) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  cases n
  · simp
  · exact spectralRadius_pow_le a _ (by simp)

end Algebra

variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

theorem isOpen_resolventSet (a : A) : IsOpen (ρ a) :=
  Units.isOpen.preimage (by fun_prop)

@[simp]
protected theorem isClosed (a : A) : IsClosed (σ a) :=
  (isOpen_resolventSet a).isClosed_compl

theorem mem_resolventSet_of_norm_lt_mul {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k ∈ ρ a := by
  rw [resolventSet, Set.mem_setOf_eq, Algebra.algebraMap_eq_smul_one]
  nontriviality A
  have hk : k ≠ 0 :=
    ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne'
  letI ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  rw [← inv_inv ‖(1 : A)‖,
    mul_inv_lt_iff₀' (inv_pos.2 <| norm_pos_iff.2 (one_ne_zero : (1 : A) ≠ 0))] at h
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : A)‖⁻¹ := by simpa [ku, norm_algebraMap] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit

theorem mem_resolventSet_of_norm_lt [NormOneClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖) : k ∈ ρ a :=
  mem_resolventSet_of_norm_lt_mul (by rwa [norm_one, mul_one])

theorem norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) : ‖k‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  le_of_not_gt <| mt mem_resolventSet_of_norm_lt_mul hk

theorem norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜} (hk : k ∈ σ a) : ‖k‖ ≤ ‖a‖ :=
  le_of_not_gt <| mt mem_resolventSet_of_norm_lt hk

theorem subset_closedBall_norm_mul (a : A) : σ a ⊆ Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖) :=
  fun k hk => by simp [norm_le_norm_mul_of_mem hk]

theorem subset_closedBall_norm [NormOneClass A] (a : A) : σ a ⊆ Metric.closedBall (0 : 𝕜) ‖a‖ :=
  fun k hk => by simp [norm_le_norm_of_mem hk]

@[simp]
theorem isBounded (a : A) : Bornology.IsBounded (σ a) :=
  Metric.isBounded_closedBall.subset (subset_closedBall_norm_mul a)

@[simp]
protected theorem isCompact [ProperSpace 𝕜] (a : A) : IsCompact (σ a) :=
  Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed a) (isBounded a)

grind_pattern spectrum.isCompact => IsCompact (spectrum 𝕜 a)

instance instCompactSpace [ProperSpace 𝕜] (a : A) : CompactSpace (spectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| spectrum.isCompact a

instance instCompactSpaceNNReal {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a : A) [CompactSpace (spectrum ℝ a)] : CompactSpace (spectrum ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap ℝ]
  exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage <| by assumption

@[simp]
theorem isCompact_nnreal {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a : A) [CompactSpace (spectrum ℝ a)] : IsCompact (spectrum ℝ≥0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern isCompact_nnreal => IsCompact (spectrum ℝ≥0 a)

section QuasispectrumCompact

variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [CompleteSpace B]
variable [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [ProperSpace 𝕜]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem _root_.quasispectrum.isCompact (a : B) : IsCompact (quasispectrum 𝕜 a) := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜,
    ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 B)]
  exact spectrum.isCompact _

grind_pattern quasispectrum.isCompact => IsCompact (quasispectrum 𝕜 a)

instance _root_.quasispectrum.instCompactSpace (a : B) :
    CompactSpace (quasispectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| quasispectrum.isCompact a

set_option backward.isDefEq.respectTransparency false in
instance _root_.quasispectrum.instCompactSpaceNNReal [NormedSpace ℝ B] [IsScalarTower ℝ B B]
    [SMulCommClass ℝ B B] (a : B) [CompactSpace (quasispectrum ℝ a)] :
    CompactSpace (quasispectrum ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← quasispectrum.preimage_algebraMap ℝ]
  exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage <| by assumption

omit [CompleteSpace B] in
@[simp]
theorem _root_.quasispectrum.isCompact_nnreal [NormedSpace ℝ B] [IsScalarTower ℝ B B]
    [SMulCommClass ℝ B B] (a : B) [CompactSpace (quasispectrum ℝ a)] :
    IsCompact (quasispectrum ℝ≥0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern quasispectrum.isCompact_nnreal => IsCompact (quasispectrum ℝ≥0 a)

end QuasispectrumCompact

section NNReal

open NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

set_option linter.style.whitespace false in -- manual alignment is not recognised
theorem le_nnnorm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ spectrum ℝ≥0 a) :
    r ≤ ‖a‖₊ := calc
  r ≤ ‖(r : ℝ)‖ := Real.le_norm_self _
  _ ≤ ‖a‖       := norm_le_norm_of_mem hr

theorem coe_le_norm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ spectrum ℝ≥0 a) :
    r ≤ ‖a‖ :=
  coe_mono <| le_nnnorm_of_mem hr

end NNReal

theorem spectralRadius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a ≤ ‖a‖₊ := by
  refine iSup₂_le fun k hk => ?_
  exact mod_cast norm_le_norm_of_mem hk

theorem exists_nnnorm_eq_spectralRadius_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty) :
    ∃ k ∈ σ a, (‖k‖₊ : ℝ≥0∞) = spectralRadius 𝕜 a := by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact a).exists_isMaxOn ha continuous_nnnorm.continuousOn
  exact ⟨k, hk, le_antisymm (le_iSup₂ (α := ℝ≥0∞) k hk) (iSup₂_le <| mod_cast h)⟩

theorem spectralRadius_lt_of_forall_lt_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty)
    {r : ℝ≥0} (hr : ∀ k ∈ σ a, ‖k‖₊ < r) : spectralRadius 𝕜 a < r :=
  sSup_image.symm.trans_lt <| ((spectrum.isCompact a).sSup_lt_iff_of_continuous ha
    continuous_enorm.continuousOn (r : ℝ≥0∞)).mpr (by simpa using hr)

open ENNReal Polynomial

variable (𝕜)

theorem spectralRadius_le_pow_nnnorm_pow_one_div (a : A) (n : ℕ) :
    spectralRadius 𝕜 a ≤ (‖a ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) *
      (‖(1 : A)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) := by
  refine iSup₂_le fun k hk => ?_
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) ∈ σ (a ^ (n + 1)) := by
    simpa only [one_mul, Algebra.algebraMap_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (@monomial 𝕜 _ (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have nnnorm_pow_le : (↑(‖k‖₊ ^ (n + 1)) : ℝ≥0∞) ≤ ‖a ^ (n + 1)‖₊ * ‖(1 : A)‖₊ := by
    simpa only [Real.toNNReal_mul (norm_nonneg _), norm_toNNReal, nnnorm_pow k (n + 1),
      ENNReal.coe_mul] using coe_mono (Real.toNNReal_mono (norm_le_norm_mul_of_mem pow_mem))
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le using 1
  all_goals dsimp
  · rw [one_div, pow_rpow_inv_natCast]
    positivity
  rw [Nat.cast_succ, ENNReal.coe_mul_rpow]

theorem spectralRadius_le_liminf_pow_nnnorm_pow_one_div (a : A) :
    spectralRadius 𝕜 a ≤ atTop.liminf fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun ε hε => ?_
  by_cases h : ε = 0
  · simp [h]
  simp only [ENNReal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_iSup_iInf_of_nat', ENNReal.iSup_mul]
  conv_rhs => arg 1; intro i; rw [ENNReal.iInf_mul (by simp [h])]
  rw [← ENNReal.inv_lt_inv, inv_one] at hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ENNReal.eventually_pow_one_div_le (ENNReal.coe_ne_top : ↑‖(1 : A)‖₊ ≠ ∞) hε)
  refine le_trans ?_ (le_iSup _ (N + 1))
  refine le_iInf fun n => ?_
  simp only [← add_assoc]
  refine (spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans ?_
  norm_cast
  grw [hN (n + N + 1) (by lia)]

end SpectrumCompact

section resolvent

open Filter Asymptotics Bornology Topology

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

theorem eventually_isUnit_resolvent (a : A) : ∀ᶠ z in cobounded 𝕜, IsUnit (resolvent a z) := by
  rw [atTop_basis_Ioi.cobounded_of_norm.eventually_iff]
  exact ⟨‖a‖ * ‖(1 : A)‖, trivial, fun _ ↦ isUnit_resolvent.mp ∘ mem_resolventSet_of_norm_lt_mul⟩

theorem resolvent_isBigO_inv (a : A) : resolvent a =O[cobounded 𝕜] Inv.inv :=
  have h : (fun z ↦ resolvent (z⁻¹ • a) (1 : 𝕜)) =O[cobounded 𝕜] (fun _ ↦ (1 : ℝ)) := by
    simpa [Function.comp_def, resolvent] using
      (NormedRing.inverse_one_sub_norm (R := A)).comp_tendsto
        (by simpa using (tendsto_inv₀_cobounded (α := 𝕜)).smul_const a)
  calc
    resolvent a =ᶠ[cobounded 𝕜] fun z ↦ z⁻¹ • resolvent (z⁻¹ • a) (1 : 𝕜) := by
      filter_upwards [isBounded_singleton (x := 0)] with z hz
      lift z to 𝕜ˣ using Ne.isUnit hz
      simpa [Units.smul_def] using congr(z⁻¹ • $(units_smul_resolvent_self (r := z) (a := a)))
    _ =O[cobounded 𝕜] (· ⁻¹) := .of_norm_right <| by
      simpa using (isBigO_refl (· ⁻¹) (cobounded 𝕜)).norm_right.smul h

theorem resolvent_tendsto_cobounded (a : A) : Tendsto (resolvent a) (cobounded 𝕜) (𝓝 0) :=
  resolvent_isBigO_inv a |>.trans_tendsto tendsto_inv₀_cobounded

end resolvent

section OneSubSMul

open ContinuousMultilinearMap ENNReal FormalMultilinearSeries

open scoped NNReal ENNReal

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

set_option backward.isDefEq.respectTransparency false in
variable (𝕜) in
/-- In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `‖a‖₊⁻¹`. -/
theorem hasFPowerSeriesOnBall_inverse_one_sub_smul [HasSummableGeomSeries A] (a : A) :
    HasFPowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) 0 ‖a‖₊⁻¹ :=
  { r_le := by
      refine le_of_forall_nnreal_lt fun r hr =>
        le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => ?_
      rw [← norm_toNNReal, norm_mkPiRing, norm_toNNReal]
      rcases n with - | n
      · simp
      · grw [nnnorm_pow_le' a n.succ_pos, ← le_max_left]
        by_cases h : ‖a‖₊ = 0
        · simp [h, pow_succ']
        · rw [← coe_inv h, coe_lt_coe, NNReal.lt_inv_iff_mul_lt h] at hr
          simpa only [← mul_pow, mul_comm] using pow_le_one' hr.le n.succ
    r_pos := ENNReal.inv_pos.mpr coe_ne_top
    hasSum := fun {y} hy => by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.eball_coe] using hy
          rwa [← coe_nnnorm, ← Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_one, nnnorm_smul,
            ← NNReal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (summable_geometric_of_norm_lt_one norm_lt).hasSum_iff] using
        (NormedRing.inverse_one_sub _ norm_lt).symm }

theorem isUnit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • (1 : A) - a) by
      rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu
    rw [Units.smul_def, ← Algebra.algebraMap_eq_smul_one, ← mem_resolventSet_iff]
    refine mem_resolventSet_of_spectralRadius_lt ?_
    rwa [Units.val_inv_eq_inv_val, nnnorm_inv,
      coe_inv (nnnorm_ne_zero_iff.mpr (Units.val_mk0 hz ▸ hz : (u : 𝕜) ≠ 0)), lt_inv_iff_lt_inv]

end OneSubSMul


section ExpMapping

local notation "↑ₐ" => algebraMap 𝕜 A

/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp` maps the spectrum of `a` into the spectrum of `exp a`. -/
theorem exp_mem_exp [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    (a : A) {z : 𝕜} (hz : z ∈ spectrum 𝕜 a) : exp z ∈ spectrum 𝕜 (exp a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ 𝕜 A
  have hexpmul : exp a = exp (a - ↑ₐ z) * ↑ₐ (exp z) := by
    rw [algebraMap_exp_comm z, ← exp_add_of_commute (Algebra.commutes z (a - ↑ₐ z)).symm,
      sub_add_cancel]
  let b := ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : ℕ => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖a - ↑ₐ z‖) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul, mul_comm, norm_inv, RCLike.norm_natCast, ← div_eq_mul_inv]
    gcongr
    · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
    · exact n.le_succ
  have h₀ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [mul_smul_comm, pow_succ'] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [pow_succ, Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum 𝕜]
    convert (expSeries_summable' (𝕂 := 𝕜) (a - ↑ₐ z)).tsum_eq_zero_add
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    · exact h₀.symm
  rw [spectrum.mem_iff, IsUnit.sub_iff, ← one_mul (↑ₐ (exp z)), hexpmul, ← _root_.sub_mul,
    Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - ↑ₐ z) - 1)).symm,
    sub_eq_iff_eq_add'.mpr h₃, Commute.isUnit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

end ExpMapping

end spectrum

namespace AlgHom

section NormedField

variable {F : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

instance (priority := 100) [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] :
    ContinuousLinearMapClass F 𝕜 A 𝕜 :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ ‖(1 : A)‖ fun a =>
        mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ _) }

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
def toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : StrongDual 𝕜 A :=
  { φ.toLinearMap with cont := map_continuous φ }

@[simp]
theorem coe_toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ :=
  rfl

theorem norm_apply_le_self_mul_norm_one [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A) :
    ‖f a‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)

theorem norm_apply_le_self [NormOneClass A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]
    (f : F) (a : A) : ‖f a‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem toContinuousLinearMap_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) :
    ‖φ.toContinuousLinearMap‖ = 1 :=
  ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one
    (fun a => (one_mul ‖a‖).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
    fun _ _ h => by simpa only [coe_toContinuousLinearMap, map_one, norm_one, mul_one] using h 1

end NontriviallyNormedField

end AlgHom

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [CompleteSpace A]
variable [NormedAlgebra 𝕜 A]

/-- The equivalence between characters and algebra homomorphisms into the base field. -/
def equivAlgHom : characterSpace 𝕜 A ≃ (A →ₐ[𝕜] 𝕜) where
  toFun := toAlgHom
  invFun f :=
    { val := f.toContinuousLinearMap
      property := by rw [eq_set_map_one_map_mul]; exact ⟨map_one f, map_mul f⟩ }

@[simp]
theorem equivAlgHom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f :=
  rfl

@[simp]
theorem equivAlgHom_symm_coe (f : A →ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f :=
  rfl

end CharacterSpace

end WeakDual

section BoundarySpectrum

local notation "σ" => spectrum

variable {𝕜 A SA : Type*} [NormedRing A] [CompleteSpace A] [SetLike SA A] [SubringClass SA A]

open Topology Filter Set

section NormedField

variable [NormedField 𝕜] [NormedAlgebra 𝕜 A] [instSMulMem : SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

open SubalgebraClass in
include instSMulMem in
/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If `a : S` is invertible in `A`,
and for all `x : S` sufficiently close to `a` within some filter `l`, `x` is invertible in `S`,
then `a` is invertible in `S` as well. -/
lemma _root_.Subalgebra.isUnit_of_isUnit_val_of_eventually {l : Filter S} {a : S}
    (ha : IsUnit (a : A)) (hla : l ≤ 𝓝 a) (hl : ∀ᶠ x in l, IsUnit x) (hl' : l.NeBot) :
    IsUnit a := by
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑ha.unit⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
    exact (NormedRing.inverse_continuousAt _).tendsto.comp <|
      continuousAt_subtype_val.tendsto.comp <| map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) ∈ S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mono fun x hx ↦ ?_
  suffices Ring.inverse (val S x) = (val S ↑hx.unit⁻¹) from this ▸ Subtype.property _
  rw [← (hx.map (val S)).unit_spec, Ring.inverse_unit (hx.map (val S)).unit, val]
  apply Units.mul_eq_one_iff_inv_eq.mp
  simpa [-IsUnit.mul_val_inv] using congr(($hx.mul_val_inv : A))

set_option backward.isDefEq.respectTransparency false in
/-- If `S : Subalgebra 𝕜 A` is a closed subalgebra of a Banach algebra `A`, then for any
`x : S`, the boundary of the spectrum of `x` relative to `S` is a subset of the spectrum of
`↑x : A` relative to `A`. -/
lemma _root_.Subalgebra.frontier_spectrum : frontier (σ 𝕜 x) ⊆ σ 𝕜 (x : A) := by
  have : CompleteSpace S := hS.completeSpace_coe
  intro μ hμ
  by_contra h
  rw [spectrum.notMem_iff] at h
  rw [← frontier_compl, (spectrum.isClosed _).isOpen_compl.frontier_eq, mem_diff] at hμ
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff, spectrum.notMem_iff]
  refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ <| .map hμ₁ (algebraMap 𝕜 S · - x)
  · calc
      _ ≤ map _ (𝓝 μ) := map_mono (by simp)
      _ ≤ _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.notMem_iff]

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the boundary of
the spectrum of `x` relative to `S` is a subset of the boundary of the spectrum of `↑x : A`
relative to `A`. -/
lemma Subalgebra.frontier_subset_frontier :
    frontier (σ 𝕜 x) ⊆ frontier (σ 𝕜 (x : A)) := by
  rw [frontier_eq_closure_inter_closure (s := σ 𝕜 (x : A)),
    (spectrum.isClosed (x : A)).closure_eq]
  apply subset_inter (frontier_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  exact inter_subset_right |>.trans <|
    closure_mono <| compl_subset_compl.mpr <| spectrum.subset_subalgebra x

open Set Notation

set_option backward.isDefEq.respectTransparency false in
/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the spectrum of `x`
is the spectrum of `↑x : A` along with the connected components of the complement of the spectrum of
`↑x : A` which contain an element of the spectrum of `x : S`. -/
lemma Subalgebra.spectrum_sUnion_connectedComponentIn :
    σ 𝕜 x = σ 𝕜 (x : A) ∪ (⋃ z ∈ (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓∩ (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn (diff_subset_compl _ _),
      union_diff_cancel (spectrum.subset_subalgebra x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq, closure_eq_interior_union_frontier,
      union_diff_distrib, diff_eq_empty.mpr (frontier_spectrum S x),
      diff_eq_compl_inter, union_empty]
    exact (spectrum.isClosed _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) ⊆ frontier (σ 𝕜 (x : A)) from
    disjoint_of_subset_left h_frontier <| disjoint_compl_right.frontier_left
      (spectrum.isClosed _).isOpen_compl
  rw [diff_eq_compl_inter]
  apply (frontier_inter_subset _ _).trans
  rw [frontier_compl]
  apply union_subset <| inter_subset_left
  refine inter_subset_inter_right _ ?_ |>.trans <| inter_subset_right
  exact frontier_subset_frontier S x

set_option backward.isDefEq.respectTransparency false in
/-- Let `S` be a closed subalgebra of a Banach algebra `A`, and let `x : S`. If `z` is in the
spectrum of `x`, then the connected component of `z` in the complement of the spectrum of `↑x : A`
is bounded (or else `z` actually belongs to the spectrum of `↑x : A`). -/
lemma Subalgebra.spectrum_isBounded_connectedComponentIn {z : 𝕜} (hz : z ∈ σ 𝕜 x) :
    Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  by_cases hz' : z ∈ σ 𝕜 (x : A)
  · simp [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
  · have : CompleteSpace S := hS.completeSpace_coe
    suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z ⊆ σ 𝕜 x from spectrum.isBounded x |>.subset this
    rw [spectrum_sUnion_connectedComponentIn S]
    exact subset_biUnion_of_mem (mem_diff_of_mem hz hz') |>.trans subset_union_right

end NormedField

variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A] [SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If for `x : S` the complement of the
spectrum of `↑x : A` is connected, then `spectrum 𝕜 x = spectrum 𝕜 (x : A)`. -/
lemma Subalgebra.spectrum_eq_of_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x : A))ᶜ) :
    σ 𝕜 x = σ 𝕜 (x : A) := by
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_sUnion_connectedComponentIn, this]
    simp
  refine eq_empty_of_forall_notMem fun z hz ↦ NormedSpace.unbounded_univ 𝕜 𝕜 ?_
  obtain ⟨hz, hz'⟩ := mem_diff _ |>.mp hz
  have := (spectrum.isBounded (x : A)).union <|
    h.connectedComponentIn hz' ▸ spectrum_isBounded_connectedComponentIn S x hz
  simpa

end BoundarySpectrum

namespace SpectrumRestricts

open NNReal ENNReal

/-- If `𝕜₁` is a normed field contained as subfield of a larger normed field `𝕜₂`, and if `a : A`
is an element whose `𝕜₂` spectrum restricts to `𝕜₁`, then the spectral radii over each scalar
field coincide. -/
lemma spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAlgebra 𝕜₂ A] [NormedAlgebra 𝕜₁ 𝕜₂]
    [IsScalarTower 𝕜₁ 𝕜₂ A] {f : 𝕜₂ → 𝕜₁} {a : A} (h : SpectrumRestricts a f) :
    spectralRadius 𝕜₁ a = spectralRadius 𝕜₂ a := by
  rw [spectralRadius, spectralRadius]
  have := algebraMap_isometry 𝕜₁ 𝕜₂ |>.nnnorm_map_of_map_zero (map_zero _)
  apply le_antisymm
  all_goals apply iSup₂_le fun x hx ↦ ?_
  · refine congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (this x) |>.symm.trans_le <| le_iSup₂ (α := ℝ≥0∞) _ ?_
    exact (spectrum.algebraMap_mem_iff _).mpr hx
  · have ⟨y, hy, hy'⟩ := h.algebraMap_image.symm ▸ hx
    subst hy'
    exact this y ▸ le_iSup₂ (α := ℝ≥0∞) y hy

variable {A : Type*} [Ring A]

lemma nnreal_iff_spectralRadius_le [Algebra ℝ A] {a : A} {t : ℝ≥0} (ht : spectralRadius ℝ a ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔
      spectralRadius ℝ (algebraMap ℝ A t - a) ≤ t := by
  have : spectrum ℝ a ⊆ Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← coe_nnnorm, NNReal.coe_le_coe,
      ← ENNReal.coe_le_coe]
    exact le_iSup₂ (α := ℝ≥0∞) x hx |>.trans ht
  rw [nnreal_iff]
  refine ⟨fun h ↦ iSup₂_le fun x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ spectrum ℝ a, ↑t - y = x := by simpa using hx
    obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp <| this hy
    lift y to ℝ≥0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : ∀ x ∈ spectrum ℝ a, ‖t - x‖₊ ≤ t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    peel h with x hx h_le
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_le] at h_le
    linarith [h_le.2]

lemma _root_.NNReal.spectralRadius_mem_spectrum {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a : A} (ha : (spectrum ℝ a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toNNReal ∈ spectrum ℝ≥0 a := by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  rw [← hx₂, ENNReal.toNNReal_coe, ← spectrum.algebraMap_mem_iff ℝ, NNReal.algebraMap_eq_coe]
  have : 0 ≤ x := ha'.rightInvOn hx₁ ▸ NNReal.zero_le_coe
  convert hx₁
  simpa

lemma _root_.Real.spectralRadius_mem_spectrum {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a : A} (ha : (spectrum ℝ a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toReal ∈ spectrum ℝ a :=
  NNReal.spectralRadius_mem_spectrum ha ha'

lemma _root_.Real.spectralRadius_mem_spectrum_or {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a : A} (ha : (spectrum ℝ a).Nonempty) :
    (spectralRadius ℝ a).toReal ∈ spectrum ℝ a ∨ -(spectralRadius ℝ a).toReal ∈ spectrum ℝ a := by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  simp only [← hx₂, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs]
  exact abs_choice x |>.imp (fun h ↦ by rwa [h]) (fun h ↦ by simpa [h])

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal
local notation "σₙ" => quasispectrum

lemma compactSpace {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [TopologicalSpace R] [TopologicalSpace S] {a : A} (f : C(S, R))
    (h : QuasispectrumRestricts a f) [h_cpct : CompactSpace (σₙ S a)] :
    CompactSpace (σₙ R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

end QuasispectrumRestricts

section UpperHemicontinuous

open Filter Set Topology

variable (𝕜 A)

lemma upperHemicontinuous_spectrum [NormedField 𝕜] [ProperSpace 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] :
    UpperHemicontinuous (spectrum 𝕜 : A → Set 𝕜) := by
  /- It suffices to use the sequential characterization of upper hemicontinuity.
  Suppose that `a : ℕ → A` converges to `a₀`, `x : ℕ → 𝕜` converges to `x₀`, and for all `n`,
  `x n ∈ spectrum 𝕜 (a n)`. -/
  rw [upperHemicontinuous_iff]
  refine fun a₀ ↦ .of_sequences
    (isCompact_closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)).isSeqCompact ?_ <|
    fun a ha x hx_mem x₀ hx ↦ ?_
  /- We must show that `spectrum 𝕜 (a n)` is eventually contained in some fixed compact set
  (we've chosen `closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)`). This follows since the spectrum of any
  `b` is bounded `‖b‖ * ‖1‖` and `a` converges to `a₀`.  -/
  · filter_upwards [Metric.closedBall_mem_nhds a₀ zero_lt_one] with a ha
    apply spectrum.subset_closedBall_norm_mul a |>.trans <| Metric.closedBall_subset_closedBall ?_
    gcongr
    apply norm_le_norm_add_norm_sub' a a₀ |>.trans
    gcongr
    simpa [dist_eq_norm] using ha
  /- Finally, `x₀ ∈ spectrum 𝕜 a₀` since `algebraMap 𝕜 A x₀ - a₀` is not invertible, being itself
  the limit of the non-invertible elements `algebraMap 𝕜 A (x n) - (a n)`. -/
  · exact nonunits.isClosed.mem_of_tendsto
      (continuous_algebraMap 𝕜 A |>.tendsto x₀ |>.comp hx |>.sub ha) <| .of_forall hx_mem

/-- The map `a ↦ spectrum ℝ≥0 a` is upper hemicontinuous. -/
theorem upperHemicontinuous_spectrum_nnreal [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    UpperHemicontinuous (spectrum ℝ≥0 : A → Set ℝ≥0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : ℝ≥0 → ℝ) := isometry_subtype_coe.isClosedEmbedding
  exact upperHemicontinuous_spectrum ℝ A |>.isInducing_comp h₁ h₂

set_option backward.isDefEq.respectTransparency false in
open WithLp in
/-- The map `a ↦ quasispectrum 𝕜 a` is upper hemicontinuous. -/
theorem upperHemicontinuous_quasispectrum [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
    [CompleteSpace A] :
    UpperHemicontinuous (quasispectrum 𝕜 : A → Set 𝕜) := by
  convert upperHemicontinuous_spectrum 𝕜 (WithLp 1 (Unitization 𝕜 A)) |>.comp
    unitization_isometry_inr.continuous
  ext1 a
  rw [Unitization.quasispectrum_eq_spectrum_inr,
    ← AlgEquiv.spectrum_eq (unitizationAlgEquiv 𝕜 (𝕜 := 𝕜) (A := A) |>.symm)]
  congr

set_option backward.isDefEq.respectTransparency false in
/-- The map `a ↦ quasispectrum ℝ≥0 a` is upper hemicontinuous. -/
theorem upperHemicontinuous_quasispectrum_nnreal [NonUnitalNormedRing A]
    [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [CompleteSpace A] :
    UpperHemicontinuous (quasispectrum ℝ≥0 : A → Set ℝ≥0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : ℝ≥0 → ℝ) := isometry_subtype_coe.isClosedEmbedding
  simpa [← NNReal.algebraMap_eq_coe] using
    upperHemicontinuous_quasispectrum ℝ A |>.isInducing_comp h₁ h₂

end UpperHemicontinuous

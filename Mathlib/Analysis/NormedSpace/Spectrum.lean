/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Topology.Algebra.Module.CharacterSpace
import Mathlib.Analysis.NormedSpace.Exponential

#align_import analysis.normed_space.spectrum from "leanprover-community/mathlib"@"d608fc5d4e69d4cc21885913fb573a88b0deb521"

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectralRadius : ℝ≥0∞`: supremum of `‖k‖₊` for all `k ∈ spectrum 𝕜 a`
* `NormedRing.algEquivComplexOfComplete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebraMap ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Main statements

* `spectrum.isOpen_resolventSet`: the resolvent set is open.
* `spectrum.isClosed`: the spectrum is closed.
* `spectrum.subset_closedBall_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.isCompact`: the spectrum is compact.
* `spectrum.spectralRadius_le_nnnorm`: the spectral radius is bounded above by the norm.
* `spectrum.hasDerivAt_resolvent`: the resolvent function is differentiable on the resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.


## TODO

* compute all derivatives of `resolvent a`.

-/


open scoped ENNReal NNReal

open NormedSpace -- For `exp`.

/-- The *spectral radius* is the supremum of the `nnnorm` (`‖·‖₊`) of elements in the spectrum,
    coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
    case, `spectralRadius a = 0`. It is also possible that `spectrum 𝕜 a` be unbounded (though
    not for Banach algebras, see `spectrum.is_bounded`, below).  In this case,
    `spectralRadius a = ∞`. -/
noncomputable def spectralRadius (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ spectrum 𝕜 a, ‖k‖₊
#align spectral_radius spectralRadius

variable {𝕜 : Type*} {A : Type*}

namespace spectrum

section SpectrumCompact

open Filter

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

local notation "σ" => spectrum 𝕜
local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem SpectralRadius.of_subsingleton [Subsingleton A] (a : A) : spectralRadius 𝕜 a = 0 := by
  simp [spectralRadius]
#align spectrum.spectral_radius.of_subsingleton spectrum.SpectralRadius.of_subsingleton

@[simp]
theorem spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0 := by
  nontriviality A
  simp [spectralRadius]
#align spectrum.spectral_radius_zero spectrum.spectralRadius_zero

theorem mem_resolventSet_of_spectralRadius_lt {a : A} {k : 𝕜} (h : spectralRadius 𝕜 a < ‖k‖₊) :
    k ∈ ρ a :=
  Classical.not_not.mp fun hn => h.not_le <| le_iSup₂ (α := ℝ≥0∞) k hn
#align spectrum.mem_resolvent_set_of_spectral_radius_lt spectrum.mem_resolventSet_of_spectralRadius_lt

variable [CompleteSpace A]

theorem isOpen_resolventSet (a : A) : IsOpen (ρ a) :=
  Units.isOpen.preimage ((continuous_algebraMap 𝕜 A).sub continuous_const)
#align spectrum.is_open_resolvent_set spectrum.isOpen_resolventSet

protected theorem isClosed (a : A) : IsClosed (σ a) :=
  (isOpen_resolventSet a).isClosed_compl
#align spectrum.is_closed spectrum.isClosed

theorem mem_resolventSet_of_norm_lt_mul {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k ∈ ρ a := by
  rw [resolventSet, Set.mem_setOf_eq, Algebra.algebraMap_eq_smul_one]
  nontriviality A
  have hk : k ≠ 0 :=
    ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne'
  letI ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  rw [← inv_inv ‖(1 : A)‖,
    mul_inv_lt_iff (inv_pos.2 <| norm_pos_iff.2 (one_ne_zero : (1 : A) ≠ 0))] at h
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : A)‖⁻¹ := by simpa [ku, norm_algebraMap] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit
#align spectrum.mem_resolvent_set_of_norm_lt_mul spectrum.mem_resolventSet_of_norm_lt_mul

theorem mem_resolventSet_of_norm_lt [NormOneClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖) : k ∈ ρ a :=
  mem_resolventSet_of_norm_lt_mul (by rwa [norm_one, mul_one])
#align spectrum.mem_resolvent_set_of_norm_lt spectrum.mem_resolventSet_of_norm_lt

theorem norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) : ‖k‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  le_of_not_lt <| mt mem_resolventSet_of_norm_lt_mul hk
#align spectrum.norm_le_norm_mul_of_mem spectrum.norm_le_norm_mul_of_mem

theorem norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜} (hk : k ∈ σ a) : ‖k‖ ≤ ‖a‖ :=
  le_of_not_lt <| mt mem_resolventSet_of_norm_lt hk
#align spectrum.norm_le_norm_of_mem spectrum.norm_le_norm_of_mem

theorem subset_closedBall_norm_mul (a : A) : σ a ⊆ Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖) :=
  fun k hk => by simp [norm_le_norm_mul_of_mem hk]
#align spectrum.subset_closed_ball_norm_mul spectrum.subset_closedBall_norm_mul

theorem subset_closedBall_norm [NormOneClass A] (a : A) : σ a ⊆ Metric.closedBall (0 : 𝕜) ‖a‖ :=
  fun k hk => by simp [norm_le_norm_of_mem hk]
#align spectrum.subset_closed_ball_norm spectrum.subset_closedBall_norm

theorem isBounded (a : A) : Bornology.IsBounded (σ a) :=
  Metric.isBounded_closedBall.subset (subset_closedBall_norm_mul a)
#align spectrum.is_bounded spectrum.isBounded

protected theorem isCompact [ProperSpace 𝕜] (a : A) : IsCompact (σ a) :=
  Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed a) (isBounded a)
#align spectrum.is_compact spectrum.isCompact

instance instCompactSpace [ProperSpace 𝕜] (a : A) : CompactSpace (spectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| spectrum.isCompact a

instance instCompactSpaceNNReal {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a : A) [CompactSpace (spectrum ℝ a)] : CompactSpace (spectrum ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap ℝ]
  exact closedEmbedding_subtype_val isClosed_nonneg |>.isCompact_preimage <| by assumption

theorem spectralRadius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a ≤ ‖a‖₊ := by
  refine' iSup₂_le fun k hk => _
  exact mod_cast norm_le_norm_of_mem hk
#align spectrum.spectral_radius_le_nnnorm spectrum.spectralRadius_le_nnnorm

theorem exists_nnnorm_eq_spectralRadius_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty) :
    ∃ k ∈ σ a, (‖k‖₊ : ℝ≥0∞) = spectralRadius 𝕜 a := by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact a).exists_forall_ge ha continuous_nnnorm.continuousOn
  exact ⟨k, hk, le_antisymm (le_iSup₂ (α := ℝ≥0∞) k hk) (iSup₂_le <| mod_cast h)⟩
#align spectrum.exists_nnnorm_eq_spectral_radius_of_nonempty spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty

theorem spectralRadius_lt_of_forall_lt_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty)
    {r : ℝ≥0} (hr : ∀ k ∈ σ a, ‖k‖₊ < r) : spectralRadius 𝕜 a < r :=
  sSup_image.symm.trans_lt <|
    ((spectrum.isCompact a).sSup_lt_iff_of_continuous ha
          (ENNReal.continuous_coe.comp continuous_nnnorm).continuousOn (r : ℝ≥0∞)).mpr
      (by dsimp only [(· ∘ ·)]; exact mod_cast hr)
#align spectrum.spectral_radius_lt_of_forall_lt_of_nonempty spectrum.spectralRadius_lt_of_forall_lt_of_nonempty

open ENNReal Polynomial

variable (𝕜)

theorem spectralRadius_le_pow_nnnorm_pow_one_div (a : A) (n : ℕ) :
    spectralRadius 𝕜 a ≤ (‖a ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) *
      (‖(1 : A)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) := by
  refine' iSup₂_le fun k hk => _
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
  rw [one_div, pow_rpow_inv_natCast]
  positivity
  rw [Nat.cast_succ, ENNReal.coe_mul_rpow]
#align spectrum.spectral_radius_le_pow_nnnorm_pow_one_div spectrum.spectralRadius_le_pow_nnnorm_pow_one_div

theorem spectralRadius_le_liminf_pow_nnnorm_pow_one_div (a : A) :
    spectralRadius 𝕜 a ≤ atTop.liminf fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) := by
  refine' ENNReal.le_of_forall_lt_one_mul_le fun ε hε => _
  by_cases h : ε = 0
  · simp only [h, zero_mul, zero_le']
  have hε' : ε⁻¹ ≠ ∞ := fun h' =>
    h (by simpa only [inv_inv, inv_top] using congr_arg (fun x : ℝ≥0∞ => x⁻¹) h')
  simp only [ENNReal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_iSup_iInf_of_nat', ENNReal.iSup_mul]
  conv_rhs => arg 1; intro i; rw [ENNReal.iInf_mul hε']
  rw [← ENNReal.inv_lt_inv, inv_one] at hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ENNReal.eventually_pow_one_div_le (ENNReal.coe_ne_top : ↑‖(1 : A)‖₊ ≠ ∞) hε)
  refine' le_trans _ (le_iSup _ (N + 1))
  refine' le_iInf fun n => _
  simp only [← add_assoc]
  refine' (spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans _
  norm_cast
  exact mul_le_mul_left' (hN (n + N + 1) (by omega)) _
#align spectrum.spectral_radius_le_liminf_pow_nnnorm_pow_one_div spectrum.spectralRadius_le_liminf_pow_nnnorm_pow_one_div

end SpectrumCompact

section resolvent

open Filter Asymptotics Bornology Topology

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

theorem hasDerivAt_resolvent {a : A} {k : 𝕜} (hk : k ∈ ρ a) :
    HasDerivAt (resolvent a) (-resolvent a k ^ 2) k := by
  have H₁ : HasFDerivAt Ring.inverse _ (↑ₐ k - a) := hasFDerivAt_ring_inverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => ↑ₐ k - a) 1 k := by
    simpa using (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit hk.unit] using H₁.comp_hasDerivAt k H₂
#align spectrum.has_deriv_at_resolvent spectrum.hasDerivAt_resolvent

-- refactored so this result was no longer necessary or useful
#noalign spectrum.norm_resolvent_le_forall

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

variable (𝕜)

/-- In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `‖a‖₊⁻¹`. -/
theorem hasFPowerSeriesOnBall_inverse_one_sub_smul [CompleteSpace A] (a : A) :
    HasFPowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) 0 ‖a‖₊⁻¹ :=
  { r_le := by
      refine'
        le_of_forall_nnreal_lt fun r hr => le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => _
      rw [← norm_toNNReal, norm_mkPiRing, norm_toNNReal]
      cases' n with n
      · simp only [Nat.zero_eq, le_refl, mul_one, or_true_iff, le_max_iff, pow_zero]
      · refine'
          le_trans (le_trans (mul_le_mul_right' (nnnorm_pow_le' a n.succ_pos) (r ^ n.succ)) _)
            (le_max_left _ _)
        · by_cases h : ‖a‖₊ = 0
          · simp only [h, zero_mul, zero_le', pow_succ]
          · rw [← coe_inv h, coe_lt_coe, NNReal.lt_inv_iff_mul_lt h] at hr
            simpa only [← mul_pow, mul_comm] using pow_le_one' hr.le n.succ
    r_pos := ENNReal.inv_pos.mpr coe_ne_top
    hasSum := fun {y} hy => by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.emetric_ball_nnreal] using hy
          rwa [← coe_nnnorm, ← Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_one, nnnorm_smul,
            ← NNReal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (NormedRing.summable_geometric_of_norm_lt_one _ norm_lt).hasSum_iff] using
        (NormedRing.inverse_one_sub _ norm_lt).symm }
#align spectrum.has_fpower_series_on_ball_inverse_one_sub_smul spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul

variable {𝕜}

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
#align spectrum.is_unit_one_sub_smul_of_lt_inv_radius spectrum.isUnit_one_sub_smul_of_lt_inv_radius

/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `fun z ↦ (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectralRadius 𝕜 a)⁻¹`. -/
theorem differentiableOn_inverse_one_sub_smul [CompleteSpace A] {a : A} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => Ring.inverse (1 - z • a)) (Metric.closedBall 0 r) := by
  intro z z_mem
  apply DifferentiableAt.differentiableWithinAt
  have hu : IsUnit (1 - z • a) := by
    refine' isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono _) hr)
    simpa only [norm_toNNReal, Real.toNNReal_coe] using
      Real.toNNReal_mono (mem_closedBall_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiableAt_inverse hu) H₁.differentiableAt
#align spectrum.differentiable_on_inverse_one_sub_smul spectrum.differentiableOn_inverse_one_sub_smul

end OneSubSMul

section GelfandFormula

open Filter ENNReal ContinuousMultilinearMap

open scoped Topology

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
theorem limsup_pow_nnnorm_pow_one_div_le_spectralRadius (a : A) :
    limsup (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop ≤ spectralRadius ℂ a := by
  refine' ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => _)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius by
    convert h
    simp only [p, p.radius_eq_liminf, ← norm_toNNReal, norm_mkPiRing]
    congr
    ext n
    rw [norm_toNNReal, ENNReal.coe_rpow_def ‖a ^ n‖₊ (1 / n : ℝ), if_neg]
    exact fun ha => (lt_self_iff_false _).mp
      (ha.2.trans_le (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ)))
  have H₁ := (differentiableOn_inverse_one_sub_smul r_lt).hasFPowerSeriesOnBall r_pos
  exact ((hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).exchange_radius H₁).r_le
#align spectrum.limsup_pow_nnnorm_pow_one_div_le_spectral_radius spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ a)) :=
  tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)
#align spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` but for `norm`
instead of `nnnorm`. -/
/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a)) := by
  convert pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  exact one_div_nonneg.mpr (mod_cast zero_le _)
#align spectrum.pow_norm_pow_one_div_tendsto_nhds_spectral_radius spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius

end GelfandFormula

section NonemptySpectrum

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A)

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
protected theorem nonempty : (spectrum ℂ a).Nonempty := by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet ℂ a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable ℂ fun z : ℂ => resolvent a z := fun z =>
    (hasDerivAt_resolvent (H₀.symm ▸ Set.mem_univ z : z ∈ resolventSet ℂ a)).differentiableAt
  /- Since `resolvent a` tends to zero at infinity, by Liouville's theorem `resolvent a = 0`,
  which contradicts that `resolvent a z` is invertible. -/
  have H₃ := H₁.apply_eq_of_tendsto_cocompact 0 <| by
    simpa [Metric.cobounded_eq_cocompact] using resolvent_tendsto_cobounded a (𝕜 := ℂ)
  exact not_isUnit_zero <| H₃ ▸ (isUnit_resolvent.mp <| H₀.symm ▸ Set.mem_univ 0)
#align spectrum.nonempty spectrum.nonempty

/-- In a complex Banach algebra, the spectral radius is always attained by some element of the
spectrum. -/
theorem exists_nnnorm_eq_spectralRadius : ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)
#align spectrum.exists_nnnorm_eq_spectral_radius spectrum.exists_nnnorm_eq_spectralRadius

/-- In a complex Banach algebra, if every element of the spectrum has norm strictly less than
`r : ℝ≥0`, then the spectral radius is also strictly less than `r`. -/
theorem spectralRadius_lt_of_forall_lt {r : ℝ≥0} (hr : ∀ z ∈ spectrum ℂ a, ‖z‖₊ < r) :
    spectralRadius ℂ a < r :=
  spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr
#align spectrum.spectral_radius_lt_of_forall_lt spectrum.spectralRadius_lt_of_forall_lt

open scoped Polynomial

open Polynomial

/-- The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`. -/
theorem map_polynomial_aeval (p : ℂ[X]) :
    spectrum ℂ (aeval a p) = (fun k => eval k p) '' spectrum ℂ a :=
  map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)
#align spectrum.map_polynomial_aeval spectrum.map_polynomial_aeval

/-- A specialization of the spectral mapping theorem for polynomials in a Banach algebra over `ℂ`
to monic monomials. -/
protected theorem map_pow (n : ℕ) :
    spectrum ℂ (a ^ n) = (· ^ n) '' spectrum ℂ a := by
  simpa only [aeval_X_pow, eval_pow, eval_X] using map_polynomial_aeval a (X ^ n)
#align spectrum.map_pow spectrum.map_pow

end NonemptySpectrum

section GelfandMazurIsomorphism

variable [NormedRing A] [NormedAlgebra ℂ A] (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0)

local notation "σ" => spectrum ℂ

theorem algebraMap_eq_of_mem {a : A} {z : ℂ} (h : z ∈ σ a) : algebraMap ℂ A z = a := by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h
#align spectrum.algebra_map_eq_of_mem spectrum.algebraMap_eq_of_mem

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebraMap ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebraMap_isometry` guarantees this map is an isometry.

Note: because `NormedDivisionRing` requires the field `norm_mul' : ∀ a b, ‖a * b‖ = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `NormedRing` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_iff_ne_zero`. -/
@[simps]
noncomputable def _root_.NormedRing.algEquivComplexOfComplete [CompleteSpace A] : ℂ ≃ₐ[ℂ] A :=
  let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId ℂ A with
    toFun := algebraMap ℂ A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using
        (@spectrum.nonempty _ _ _ _ nt <| algebraMap ℂ A z).some_mem
    right_inv := fun a => algebraMap_eq_of_mem (@hA) (@spectrum.nonempty _ _ _ _ nt a).some_mem }
#align normed_ring.alg_equiv_complex_of_complete NormedRing.algEquivComplexOfComplete

end GelfandMazurIsomorphism

section ExpMapping

local notation "↑ₐ" => algebraMap 𝕜 A

/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp` maps the spectrum of `a` into the spectrum of `exp a`. -/
theorem exp_mem_exp [IsROrC 𝕜] [NormedRing A] [Algebra ℚ A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    (a : A) {z : 𝕜} (hz : z ∈ spectrum 𝕜 a) : exp z ∈ spectrum 𝕜 (exp a) := by
  have hexpmul : exp a = exp (a - ↑ₐ z) * ↑ₐ (exp z) := by
    rw [algebraMap_exp_comm z, ← exp_add_of_commute 𝕜 (Algebra.commutes z (a - ↑ₐ z)).symm,
      sub_add_cancel]
  let b := ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : ℕ => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine' .of_norm_bounded_eventually _ (Real.summable_pow_div_factorial ‖a - ↑ₐ z‖) _
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul, mul_comm, norm_inv, IsROrC.norm_natCast, ← div_eq_mul_inv]
    exact div_le_div (pow_nonneg (norm_nonneg _) n) (norm_pow_le' (a - ↑ₐ z) (zero_lt_iff.mpr hn))
      (mod_cast Nat.factorial_pos n) (mod_cast Nat.factorial_le (lt_add_one n).le)
  have h₀ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [mul_smul_comm, pow_succ] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [pow_succ', Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum]
    convert tsum_eq_zero_add (expSeries_summable' (𝕂 := 𝕜) (a - ↑ₐ z))
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    convert h₀.symm
    ext a
    exact inv_nat_cast_smul_eq ℚ 𝕜 _ a
  rw [spectrum.mem_iff, IsUnit.sub_iff, ← one_mul (↑ₐ (exp z)), hexpmul, ← _root_.sub_mul,
    Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - ↑ₐ z) - 1)).symm,
    sub_eq_iff_eq_add'.mpr h₃, Commute.isUnit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))
#align spectrum.exp_mem_exp spectrum.exp_mem_exp

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
def toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
  { φ.toLinearMap with cont := map_continuous φ }
#align alg_hom.to_continuous_linear_map AlgHom.toContinuousLinearMap

@[simp]
theorem coe_toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ :=
  rfl
#align alg_hom.coe_to_continuous_linear_map AlgHom.coe_toContinuousLinearMap

theorem norm_apply_le_self_mul_norm_one [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A) :
    ‖f a‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)
#align alg_hom.norm_apply_le_self_mul_norm_one AlgHom.norm_apply_le_self_mul_norm_one

theorem norm_apply_le_self [NormOneClass A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]
    (f : F) (a : A) : ‖f a‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)
#align alg_hom.norm_apply_le_self AlgHom.norm_apply_le_self

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
#align alg_hom.to_continuous_linear_map_norm AlgHom.toContinuousLinearMap_norm

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
  left_inv f := Subtype.ext <| ContinuousLinearMap.ext fun x => rfl
  right_inv f := AlgHom.ext fun x => rfl
#align weak_dual.character_space.equiv_alg_hom WeakDual.CharacterSpace.equivAlgHom

@[simp]
theorem equivAlgHom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f :=
  rfl
#align weak_dual.character_space.equiv_alg_hom_coe WeakDual.CharacterSpace.equivAlgHom_coe

@[simp]
theorem equivAlgHom_symm_coe (f : A →ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f :=
  rfl
#align weak_dual.character_space.equiv_alg_hom_symm_coe WeakDual.CharacterSpace.equivAlgHom_symm_coe

end CharacterSpace

end WeakDual

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

lemma nnreal_iff [Algebra ℝ A] {a : A} :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ spectrum ℝ a, 0 ≤ x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap _ _ (fun _ ↦ Real.toNNReal_coe)
      fun x hx ↦ ⟨⟨x, h x hx⟩, rfl⟩

lemma real_iff [Algebra ℂ A] {a : A} :
    SpectrumRestricts a Complex.reCLM ↔ ∀ x ∈ spectrum ℂ a, x = x.re := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    simp
  · exact .of_subset_range_algebraMap _ _ Complex.ofReal_re fun x hx ↦ ⟨x.re, (h x hx).symm⟩

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

end SpectrumRestricts

/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.LSeries.Basic

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The Wiener-Ikehara Tauberian theorem

Let `f : ℕ → ℝ` be non-negative with `∑ n ≤ x, f n ≪ x`, whose `L`-series `F` extends
continuously to `Re s ≥ 1` after subtracting `A / (s - 1)`.  Then
`∑ n < N, f n = A * N + o(N)`. These hypotheses are bundled in `IsWienerIkehara f C A G`, where
`C` is the implied constant in `∑ n ≤ x, f n ≪ x` and `G` is the continuous extension.

The classical theorem does not need the bound `∑ n ≤ x, f n ≪ x`, only the convergence of `F(s)`
for `Re s > 1` (which the bound implies); it is assumed here because it simplifies the proof.

## Main results

* `WienerIkehara.tendsto_sum_div`, `WienerIkehara.tendsto_sum_range_div`: the Wiener-Ikehara
Tauberian theorem, summing over reals `n ≤ x` and over naturals `n < N` respectively.
* `WienerIkehara.tendsto_sum_div_smooth`, `WienerIkehara.tendsto_sum_div_smooth_real`: versions
for smooth cutoffs.
* `IsWienerIkehara.A_nonneg`: the residue `A` is non-negative.

## Proof outline

Writing `ψ̂` for the Fourier transform, the proof studies `remainder f A σ ψ̂ x`, the difference
between `∑' n, term f σ n * ψ̂ (log (n / x) / (2 * π))` and its polar counterpart.  Rewriting both
halves as Fourier integrals (`smoothedSum_fourier_eq`, `poleTerm_fourier_eq`) cancels the
pole and expresses `remainder` through `G` (`remainder_fourier_eq`); letting `σ → 1` and applying
the Riemann-Lebesgue lemma gives `remainder f A 1 ψ̂ x → 0`, first for compactly supported test
functions (`tendsto_remainder_one_fourier_of_hasCompactSupport`) and then for all Schwartz
functions (`tendsto_remainder_one_fourier`).
Surjectivity of the Fourier transform on Schwartz space upgrades this to a smoothed form of the
theorem (`tendsto_sum_div_smooth_real`), and non-negativity of `f` together with smooth cutoffs
(`Real.exists_contDiff_indicator_Icc_le_le_indicator_Ioo`) replaces the smooth cutoff by the
indicator of an interval, whence the theorem (`tendsto_sum_div`).

This file is adapted from the `PrimeNumberTheoremAnd` project.
-/

noncomputable section

open Complex hiding log
open Real MeasureTheory Filter Set FourierTransform LSeries Asymptotics SchwartzMap
  Function
open scoped Topology ContDiff ComplexConjugate LSeries.notation

/-- The hypotheses of the Wiener-Ikehara theorem: `f : ℕ → ℝ` is non-negative and obeys the
Chebyshev-type bound `∑ i < n, f i ≤ C * n`, and `G` is a continuous extension of
`s ↦ LSeries f s - A / (s - 1)` from the open half-plane `1 < re s` to the closed half-plane
`1 ≤ re s`. -/
public structure IsWienerIkehara (f : ℕ → ℝ) (C A : ℝ) (G : ℂ → ℂ) : Prop where
  /-- `f` is non-negative. -/
  nonneg : 0 ≤ f
  /-- The partial sums of `f` grow at most linearly, with constant `C`. -/
  sum_range_le (n : ℕ) : ∑ i ∈ .range n, f i ≤ C * n
  /-- `G` is continuous on the closed half-plane `1 ≤ re s`. -/
  continuousOn : ContinuousOn G {s | 1 ≤ s.re}
  /-- `G` agrees with `LSeries f s - A / (s - 1)` on the open half-plane `1 < re s`. -/
  eqOn : EqOn G (fun s ↦ LSeries ↗f s - A / (s - 1)) {s | 1 < s.re}

namespace IsWienerIkehara

variable {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ}

/-- The constant `C` in the hypotheses of the Wiener-Ikehara theorem is non-negative. -/
public lemma C_nonneg (h : IsWienerIkehara f C A G) : 0 ≤ C :=
  (h.nonneg 0).trans (by simpa using h.sum_range_le 1)

end IsWienerIkehara

namespace WienerIkehara

section FourierSeminorm

variable (ψ : 𝓢(ℝ, ℂ)) (u : ℝ)

/-- A bespoke seminorm on Schwartz functions `ψ` controlling the decay of their Fourier transform:
`‖𝓕 ψ u‖ ≤ fourierSeminorm ψ / (1 + u ^ 2)`, see `norm_fourier_le_fourierSeminorm_mul`. -/
abbrev fourierSeminorm : ℝ := (𝓕 ψ).seminorm ℝ 0 0 + (𝓕 ψ).seminorm ℝ 2 0

lemma fourierSeminorm_nonneg : 0 ≤ fourierSeminorm ψ := by
  positivity

lemma continuous_fourierSeminorm : Continuous fourierSeminorm := by
  fun_prop

lemma norm_fourier_le_fourierSeminorm_mul : ‖𝓕 ψ u‖ ≤ fourierSeminorm ψ * (1 + u ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2), fourierSeminorm]
  have h := norm_pow_mul_le_seminorm ℝ (𝓕 ψ) 2 u
  rw [Real.norm_eq_abs, sq_abs] at h
  linarith [norm_le_seminorm ℝ (𝓕 ψ) u]

end FourierSeminorm

variable (f : ℕ → ℝ) (A : ℝ) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ)

/-- The smoothed sum `∑' n, term f σ n * φ ((2 * π)⁻¹ * log (n / x))` of `f` against a test
function `φ` at the scale `x`. -/
def smoothedSum : ℂ := ∑' n, term ↗f σ n * φ ((2 * π)⁻¹ * log (n / x))

/-- The contribution to `smoothedSum` of a pole of `LSeries f` at `s = 1` with residue `A`. -/
def poleTerm : ℂ :=
  A * ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x), rexp (-u * (σ - 1)) * φ ((2 * π)⁻¹ * u)

/-- A key statistic in the Wiener--Ikehara analysis involving an exponent `σ`, a test
function `φ`, and a scale parameter `x`: the smoothed sum of `f` minus the contribution of the
pole of its `L`-series. -/
def remainder : ℂ := smoothedSum f σ φ x - poleTerm A σ φ x

lemma poleTerm_one : poleTerm A 1 φ x = A * ∫ u in Ici (-log x), φ ((2 * π)⁻¹ * u) := by
  simp [poleTerm]

variable {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ} (h : IsWienerIkehara f C A G)

section FourierIdentities

variable {x σ : ℝ} (ψ : 𝓢(ℝ, ℂ)) (hx : 0 < x) (hσ : 1 < σ)

include h hx hσ in
lemma smoothedSum_fourier_eq :
    smoothedSum f σ (𝓕 ψ) x = ∫ t : ℝ, LSeries ↗f (σ + t * I) * ψ t * x ^ (t * I) :=
  calc
    _ = ∑' n, ∫ t, term ↗f σ n * 𝐞 (-((2 * π)⁻¹ * log (n / x) * t)) • ψ t := by
      simp [smoothedSum, fourier_coe, fourier_eq, integral_const_mul]
    _ = ∫ t, ∑' n, _ := by
      refine integral_tsum_of_summable_integral_norm (fun n ↦ ?_) ?_
      · exact (ψ.integrable.norm.const_mul ‖term ↗f σ n‖).mono' (by fun_prop)
          (.of_forall fun t ↦ by simp)
      · simpa [integral_const_mul] using (LSeriesSummable_of_sum_range_le_and_nonneg
          h.sum_range_le h.nonneg (by simpa using hσ)).norm.mul_right (∫ t, ‖ψ t‖)
    _ = _ := by
      congr with t
      rw [LSeries, mul_assoc, ← tsum_mul_right]
      congr with n
      by_cases hn : n = 0
      · simp_all
      have hn' : (0 : ℝ) < n := by positivity
      have harg : -((2 * π)⁻¹ * log (n / x) * t) = t * log x / (2 * π) - t * log n / (2 * π) := by
        rw [log_div hn'.ne' hx.ne']
        ring
      rw [harg, AddChar.map_sub_eq_div, Circle.smul_def, Circle.coe_div,
        fourierChar_mul_log_div_two_pi hx, fourierChar_mul_log_div_two_pi hn']
      simp [cpow_add, field, *]

include hx hσ in
lemma poleTerm_fourier_eq :
    poleTerm A σ (𝓕 ψ) x = A * ∫ t, (1 / (σ + t * I - 1)) * ψ t * x ^ (t * I) := by
  have hint : IntegrableOn (fun u ↦ rexp (-u * (σ - 1))) (Ici (-log x)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    convert exp_neg_integrableOn_Ioi (-log x) (sub_pos.mpr hσ) using 1
    grind
  rw [poleTerm, mul_assoc]
  congr 1
  calc
    _ = ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x),
        ∫ t, (rexp (-u * (σ - 1)) : ℂ) • 𝐞 (-(t * ((2 * π)⁻¹ * u))) • ψ t := by
      simp_rw [fourier_coe, fourier_real_eq, ← smul_eq_mul, ← integral_smul]
    _ = ↑(x ^ (1 - σ)) * ∫ t, ∫ u in Ici (-log x), _ :=
      congr(_ * $(integral_integral_swap ((Integrable.mul_prod hint ψ.integrable.norm).mono'
        (by fun_prop) (.of_forall fun ⟨u, t⟩ ↦ by simp [Complex.norm_exp]))))
    _ = _ := by
      rw [← integral_const_mul]
      congr with t
      simp_rw [Circle.smul_def, smul_smul, smul_eq_mul, integral_mul_const]
      have hI : ∫ u in Ici (-log x), (rexp (-u * (σ - 1)) : ℂ) * 𝐞 (-(t * ((2 * π)⁻¹ * u))) =
          ∫ u in Ioi (-log x), cexp (-(σ - 1 + t * I) * u) := by
        rw [integral_Ici_eq_integral_Ioi]
        congr with u
        push_cast [fourierChar_apply, ← Complex.exp_add]
        congr
        field
      have hx' : (x : ℂ) ≠ 0 := mod_cast hx.ne'
      rw [← mul_assoc, hI, integral_cexp_neg_mul_Ioi_neg_log hx (by simpa using hσ),
        ofReal_cpow hx.le, mul_div_assoc', ← cpow_add _ _ hx']
      push_cast
      rw [show 1 - (σ : ℂ) + (σ - 1 + t * I) = t * I by ring]
      ring

include h hx in
/-- The main result of this section: an initial Fourier identity expressing a sum of
`f` as an error term of Fourier integral type. -/
lemma remainder_fourier_eq {ψ : 𝓢(ℝ, ℂ)} (hψ : HasCompactSupport ψ) {σ : ℝ} (hσ : 1 < σ) :
    remainder f A σ (𝓕 ψ) x = ∫ t : ℝ, G (σ + t * I) * ψ t * x ^ (t * I) := by
  have hσt (t : ℝ) : 1 < (σ + t * I).re := by simpa using hσ
  have (t : ℝ) : (σ : ℂ) + t * I - 1 ≠ 0 := ne_zero_of_re_pos (by simpa using hσ)
  have hcpow : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) := by fun_prop (disch := simp [hx.ne'])
  have hGc : Continuous fun t : ℝ ↦ G (σ + t * I) :=
    h.continuousOn.comp_continuous (by fun_prop) fun t ↦ (hσt t).le
  have hint₁ : Integrable fun t : ℝ ↦ G (σ + t * I) * ψ t * x ^ (t * I) :=
    ((hGc.mul ψ.continuous).mul hcpow).integrable_of_hasCompactSupport hψ.mul_left.mul_right
  have hint₂ : Integrable fun t : ℝ ↦ A * (1 / (σ + t * I - 1) * ψ t * x ^ (t * I)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ.mul_left.mul_right.mul_left
  rw [remainder, smoothedSum_fourier_eq h ψ hx hσ, poleTerm_fourier_eq ψ hx hσ,
    sub_eq_iff_eq_add, ← integral_const_mul, ← integral_add hint₁ hint₂]
  exact integral_congr_ae (.of_forall fun t ↦ by grind [h.eqOn (hσt t)])

end FourierIdentities

section Weight

variable {a c t x : ℝ} {n : ℕ}

/-- A weight function appearing in the analysis. -/
def weight (t : ℝ) : ℝ := (t * (1 + ((2 * π)⁻¹ * log t) ^ 2))⁻¹

lemma weight_nonneg (ht : 0 ≤ t) : 0 ≤ weight t := by rw [weight]; positivity

lemma hasDerivAt_weight (ht : t ≠ 0) : HasDerivAt weight
    (-((2 * π)⁻¹ ^ 2 * (log t + 1) ^ 2 + (1 - (2 * π)⁻¹) * (1 + (2 * π)⁻¹)) * weight t ^ 2) t := by
  have : HasDerivAt (fun t ↦ t * (1 + ((2 * π)⁻¹ * log t) ^ 2))
      (1 + 2 * (2 * π)⁻¹ ^ 2 * log t + ((2 * π)⁻¹ * log t) ^ 2) t := by
    convert (hasDerivAt_id' t).mul ?_ (d' := 2 * (2 * π)⁻¹ ^ 2 * t⁻¹ * log t) using 1
    · grind
    convert (((hasDerivAt_log ht).const_mul _).pow (f' := (2 * π)⁻¹ * t⁻¹) 2).const_add _ using 1
    ring
  unfold weight
  convert this.inv (by positivity) using 1
  grind

lemma antitoneOn_weight : AntitoneOn weight (Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
    (fun _ _ ↦ (hasDerivAt_weight (by grind)).continuousAt.continuousWithinAt)
    (fun _ _ ↦ (hasDerivAt_weight (fun _ ↦ by simp_all)).hasDerivWithinAt)
    fun x _ ↦ ?_
  have : 0 < 1 - (2 * π)⁻¹ := by grind [two_le_pi, inv_lt_one_of_one_lt₀]
  simp only [neg_mul, Left.neg_nonpos_iff]
  positivity

lemma integrableOn_mul_weight_div (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * weight (t / c)) (Ici 0) := by
  have (t) (ht : 0 < t) :
      t⁻¹ • (a * c * (1 + ((2 * π)⁻¹ * (log t - log c)) ^ 2)⁻¹) = a * weight (t / c) := by
    have : 0 < 1 + ((2 * π)⁻¹ * (log t - log c)) ^ 2 := by positivity
    simp [weight, log_div ht.ne' hc.ne', field]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact ((integrableOn_comp_log_Ioi_zero _).2
    (((integrable_inv_one_add_mul_sq (by positivity)).comp_sub_right _).const_mul _)).congr_fun
    this measurableSet_Ioi

lemma antitoneOn_inv_mul_weight_div (hx : 0 < x) :
    AntitoneOn (fun t ↦ x⁻¹ * weight (t / x)) (Ioc 0 n) := by
  intro u hu v hv huv
  dsimp only
  gcongr
  exact antitoneOn_weight (div_pos hu.1 hx) (div_pos hv.1 hx) (by gcongr)

lemma integrableOn_inv_mul_weight_div (hx : 0 < x) :
    IntegrableOn (fun t ↦ x⁻¹ * weight (t / x)) (Icc 0 n) :=
  .mono_set (integrableOn_mul_weight_div (by positivity)) Icc_subset_Ici_self

lemma inv_mul_weight_div (hx : x ≠ 0) (t : ℝ) :
    x⁻¹ * weight (t / x) = (t * (1 + ((2 * π)⁻¹ * log (t / x)) ^ 2))⁻¹ := by
  grind [weight]

lemma inv_mul_weight_div_le_one (hx : x ≠ 0) (ht : 1 ≤ t) : x⁻¹ * weight (t / x) ≤ 1 := by
  rw [inv_mul_weight_div hx]
  exact inv_le_one_of_one_le₀ <| one_le_mul_of_one_le_of_one_le ht <|
    le_add_of_nonneg_right (sq_nonneg _)

lemma antitone_ite_weight (hx : 0 < x) :
    Antitone fun i : ℕ ↦ if i = 0 then (1 : ℝ) else x⁻¹ * weight (i / x) := by
  intro i j hij
  rcases eq_or_ne j 0 with rfl | hj
  · grind
  simp only [hj, ↓reduceIte]
  split_ifs with hi
  · exact inv_mul_weight_div_le_one hx.ne' (mod_cast by grind)
  · gcongr
    exact antitoneOn_weight (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity)) (by gcongr)

end Weight

section LimitingFourierIdentity

variable {x : ℝ} (Ψ : 𝓢(ℝ, ℂ)) (hΨ : HasCompactSupport Ψ) (hx : 1 ≤ x) (n : ℕ)

include hx in
lemma sum_range_ite_weight_le :
    ∑ i ∈ .range n, (if i = 0 then 1 else x⁻¹ * weight (i / x)) ≤
      1 + ∫ t in Ioi 0, weight t := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rcases n with _ | m
  · simpa using add_nonneg zero_le_one
      (setIntegral_nonneg measurableSet_Ioi fun t ht ↦ weight_nonneg ht.le)
  simp only [Finset.sum_range_succ', Nat.add_one_ne_zero, ↓reduceIte]
  rw [add_comm _ (1 : ℝ)]
  gcongr
  calc
    _ ≤ ∫ t in 0..m, x⁻¹ * weight (t / x) := by
      simpa using @AntitoneOn.sum_le_integral_of_integrableOn 0 m (fun t ↦ x⁻¹ * weight (t / x))
        (by simpa using antitoneOn_inv_mul_weight_div hx₀)
        (by simpa using integrableOn_inv_mul_weight_div hx₀)
    _ = ∫ t in 0..m / x, weight t := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div weight hx₀.ne',
        zero_div, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hx₀.ne', one_mul]
    _ ≤ ∫ t in Ioi 0, weight t := by
      rw [intervalIntegral.integral_of_le (by positivity)]
      exact setIntegral_mono_set
        (by simpa using
          (integrableOn_mul_weight_div (a := 1) zero_lt_one).mono_set Ioi_subset_Ici_self)
        (eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun t ht ↦ weight_nonneg ht.le)
        Ioc_subset_Ioi_self.eventuallyLE

include h hx in
lemma bound_sum_log_range :
    ∑ i ∈ .range n, ‖f i‖ / i * (1 + ((2 * π)⁻¹ * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, weight t) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have := h.C_nonneg
  calc
    _ ≤ ∑ i ∈ .range n, ‖f i‖ * (if i = 0 then 1 else x⁻¹ * weight (i / x)) := by
      gcongr 1 with i
      by_cases i = 0 <;> simp [*, weight, field]
    _ ≤ ∑ i ∈ .range n, C * (if i = 0 then 1 else x⁻¹ * weight (i / x)) :=
      Finset.sum_mul_le_sum_mul_of_sum_range_le
        (fun k _ ↦ by simpa [mul_comm, Real.norm_of_nonneg (h.nonneg _)] using h.sum_range_le k)
        (fun i ↦ by
          unfold weight
          simp only [Pi.zero_apply]
          positivity)
        ((antitone_ite_weight hx₀).antitoneOn _)
    _ ≤ C * (1 + ∫ t in Ioi 0, weight t) := by
      rw [← Finset.mul_sum]
      gcongr
      exact sum_range_ite_weight_le hx n

include h hx in
lemma summable_sum_log_range :
    Summable fun n ↦ ‖f n‖ / n * (1 + ((2 * π)⁻¹ * log (n / x)) ^ 2)⁻¹ :=
  summable_of_sum_range_le (fun _ ↦ by positivity)
    fun n ↦ by simpa using bound_sum_log_range h hx n

lemma norm_term_mul_le (x : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    ‖term f 1 n * 𝓕 Ψ ((2 * π)⁻¹ * log (n / x))‖ ≤
      fourierSeminorm Ψ * (‖f n‖ / n * (1 + ((2 * π)⁻¹ * log (n / x)) ^ 2)⁻¹) := by
  convert mul_le_mul_of_nonneg_left
    (norm_fourier_le_fourierSeminorm_mul Ψ ((2 * π)⁻¹ * log (n / x)))
    (norm_nonneg (f n / n)) using 1
  · simp [term_of_ne_zero']
  · rw [norm_div, Complex.norm_natCast]
    ring

include h hx in
lemma tendsto_smoothedSum :
    Tendsto (smoothedSum f · (𝓕 Ψ) x) (𝓝[>] 1) (𝓝 (smoothedSum f 1 (𝓕 Ψ) x)) := by
  simp only [smoothedSum]
  refine tendsto_tsum_of_dominated_convergence
    ((summable_sum_log_range h hx).mul_left (fourierSeminorm Ψ)) (fun n ↦ ?_) ?_
  · refine (Continuous.tendsto ?_ 1).mono_left nhdsWithin_le_nhds
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [term] using continuous_const
    · simp only [term, hn, ↓reduceIte]
      fun_prop (disch := simp [hn])
  · refine eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) n ↦ ?_
    refine le_trans ?_ ((norm_term_mul_le Ψ x ↗f n).trans_eq (by simp))
    simp only [norm_mul]
    gcongr
    exact norm_term_le_of_re_le_re _ (by simpa using hσ.le) n

include hx in
lemma tendsto_poleTerm :
    Tendsto (poleTerm A · (𝓕 Ψ) x) (𝓝[>] 1) (𝓝 (poleTerm A 1 (𝓕 Ψ) x)) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  apply Tendsto.mul
  · exact (Continuous.tendsto (by fun_prop (disch := simp [hx₀.ne'])) 1).mono_left
      nhdsWithin_le_nhds
  refine tendsto_integral_filter_of_dominated_convergence (fun t ↦ x * ‖𝓕 Ψ ((2 * π)⁻¹ * t)‖)
    (.of_forall fun _ ↦ Continuous.aestronglyMeasurable (by fun_prop)) ?_
    (((𝓕 Ψ).integrable.comp_mul_left' (by positivity)).norm.const_mul x).restrict
    (.of_forall fun t ↦ (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT one_lt_two] with σ ⟨hσ₁, hσ₂⟩
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t (ht : -log x ≤ t)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_nonneg _)]
  gcongr
  calc
    rexp (-t * (σ - 1)) ≤ rexp (log x) := exp_le_exp.mpr (by nlinarith [log_nonneg hx])
    _ = x := exp_log hx₀

include h hΨ in
lemma tendsto_remainder_one_fourier_of_hasCompactSupport :
    Tendsto (remainder f A 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  refine (tendsto_integral_cpow_mul_I_smul_atTop fun t ↦ G (1 + t * I) * Ψ t).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hcpow : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) := by
    fun_prop (disch := simp [(zero_lt_one.trans_le hx).ne'])
  have hcont : ContinuousOn (fun σ : ℝ ↦ ∫ t : ℝ, G (σ + t * I) * Ψ t * x ^ (t * I)) (Ici 1) := by
    refine continuousOn_integral_of_compact_support hΨ.isCompact ?_ fun σ t _ ht ↦ by
      simp [image_eq_zero_of_notMem_tsupport ht]
    refine ((h.continuousOn.comp (by fun_prop) fun p hp ↦ ?_).mul
      (Ψ.continuous.comp continuous_snd).continuousOn).mul (hcpow.comp continuous_snd).continuousOn
    simpa using (mem_prod.mp hp).1
  rw [remainder, tendsto_nhds_unique_of_eventuallyEq
    ((tendsto_smoothedSum h Ψ hx).sub (tendsto_poleTerm Ψ hx))
    ((hcont 1 self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))
    (eventuallyEq_nhdsWithin_iff.mpr <| .of_forall fun σ hσ ↦
      remainder_fourier_eq h (by linarith) hΨ hσ)]
  simp only [ofReal_one, smul_eq_mul]
  congr with t
  ring

end LimitingFourierIdentity

section LimitingFourierIdentitySchwartz

variable (Ψ φ φ' : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 1 ≤ x)

lemma norm_setIntegral_fourier_le (x : ℝ) :
    ‖∫ u in Ici (-log x), 𝓕 Ψ ((2 * π)⁻¹ * u)‖ ≤
      fourierSeminorm Ψ * ∫ u, (1 + ((2 * π)⁻¹ * u) ^ 2)⁻¹ := by
  have hint : Integrable fun u : ℝ ↦ fourierSeminorm Ψ * (1 + ((2 * π)⁻¹ * u) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' (by positivity)).const_mul _
  rw [← integral_const_mul]
  exact (norm_integral_le_of_norm_le hint.integrableOn
    (.of_forall fun u ↦ norm_fourier_le_fourierSeminorm_mul Ψ _)).trans
    (setIntegral_le_integral hint
      (.of_forall fun _ ↦ mul_nonneg (fourierSeminorm_nonneg Ψ) (by positivity)))

include h hx in
lemma summable_term_mul : Summable fun n ↦ ‖term ↗f 1 n * 𝓕 Ψ ((2 * π)⁻¹ * log (n / x))‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_mul_le Ψ x ↗f)
    (by simpa using (summable_sum_log_range h hx).const_smul (fourierSeminorm Ψ))

include h hx in
/-- The map `φ ↦ remainder f A 1 (𝓕 φ) x` is linear in the test function. -/
lemma remainder_one_fourier_sub :
    remainder f A 1 (𝓕 (φ - φ')) x = remainder f A 1 (𝓕 φ) x - remainder f A 1 (𝓕 φ') x := by
  have hs (ψ : 𝓢(ℝ, ℂ)) := (summable_term_mul h ψ hx).of_norm
  have hi (ψ : 𝓢(ℝ, ℂ)) : IntegrableOn (fun u ↦ 𝓕 ψ ((2 * π)⁻¹ * u)) (Ici (-log x)) :=
    ((𝓕 ψ).integrable.comp_mul_left' (by positivity)).integrableOn
  simp only [remainder, smoothedSum, poleTerm_one, fourier_sub, sub_apply, mul_sub, ofReal_one]
  rw [Summable.tsum_sub (hs φ) (hs φ'), integral_sub (hi φ) (hi φ')]
  ring

include h in
/-- `φ ↦ remainder f A 1 (𝓕 φ) x` is bounded by a multiple of the seminorm `fourierSeminorm φ`,
uniformly in `x ≥ 1`. -/
lemma exists_norm_remainder_one_le :
    ∃ K, ∀ (φ : 𝓢(ℝ, ℂ)) {x : ℝ}, 1 ≤ x → ‖remainder f A 1 (𝓕 φ) x‖ ≤ fourierSeminorm φ * K := by
  refine ⟨C * (1 + ∫ t in Ioi 0, weight t) + |A| * ∫ u, (1 + ((2 * π)⁻¹ * u) ^ 2)⁻¹,
    fun φ x hx ↦ ?_⟩
  have h₁ : ‖smoothedSum f 1 (𝓕 φ) x‖ ≤
      fourierSeminorm φ * (C * (1 + ∫ t in Ioi 0, weight t)) := by
    rw [smoothedSum, ofReal_one]
    refine (norm_tsum_le_tsum_norm (summable_term_mul h φ hx)).trans ?_
    calc
      _ ≤ ∑' n, fourierSeminorm φ * (‖f n‖ / n * (1 + ((2 * π)⁻¹ * log (n / x)) ^ 2)⁻¹) :=
        (summable_term_mul h φ hx).tsum_mono
          ((summable_sum_log_range h hx).mul_left _)
          fun n ↦ (norm_term_mul_le φ x ↗f n).trans_eq (by simp)
      _ ≤ _ := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (tsum_le_of_sum_range_le (fun _ ↦ by positivity)
          (bound_sum_log_range h hx)) (fourierSeminorm_nonneg φ)
  have h₂ : ‖poleTerm A 1 (𝓕 φ) x‖ ≤
      fourierSeminorm φ * (|A| * ∫ u, (1 + ((2 * π)⁻¹ * u) ^ 2)⁻¹) := by
    simp only [poleTerm_one, norm_mul, norm_real, norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (norm_setIntegral_fourier_le φ x) (abs_nonneg A)).trans_eq
      (by ring)
  grind [remainder, norm_sub_le]

include h in
lemma tendsto_remainder_one_fourier : Tendsto (remainder f A 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_norm_remainder_one_le h
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨φ, hφQ : _ < ε / 2, hφcs⟩ := SchwartzMap.dense_hasCompactSupport.inter_open_nonempty
    {φ | fourierSeminorm (Ψ - φ) * K < ε / 2}
    (isOpen_lt ((continuous_fourierSeminorm.comp (by fun_prop)).mul continuous_const)
      continuous_const)
    ⟨Ψ, by simpa [fourierSeminorm] using half_pos hε⟩
  filter_upwards [eventually_ge_atTop 1, Metric.tendsto_nhds.mp
    (tendsto_remainder_one_fourier_of_hasCompactSupport h φ hφcs) (ε / 2)
    (half_pos hε)] with x hx hφ
  rw [dist_zero_right] at hφ ⊢
  grind [remainder_one_fourier_sub h Ψ φ hx, norm_sub_norm_le, hK (Ψ - φ) hx]

end LimitingFourierIdentitySchwartz

section Smooth

variable {ψ : ℝ → ℂ} (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (hplus : tsupport ψ ⊆ Ioi 0)

include h hsmooth hsupp hplus in
/-- A smoothed *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function with `∑ i < n, f i ≤ C * n` whose L-series has a simple pole at `s = 1` with residue `A`
and otherwise extends continuously to the closed half-plane `re s ≥ 1`, then `f` behaves like `A`
asymptotically with respect to smooth weights with compact support in `(0, ∞)`. -/
public lemma tendsto_sum_div_smooth : Tendsto (fun x ↦ (∑' n, f n * ψ (n / x)) / x)
    atTop (𝓝 (A * ∫ y in Ioi 0, ψ y)) := by
  have hψ₀ : ψ =ᶠ[𝓝 0] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h₀ ↦ lt_irrefl 0 (hplus h₀)
  -- `y ↦ y * ψ y`, written in the variable `(2 * π)⁻¹ * log y`, is a Fourier transform.
  obtain ⟨g, hg⟩ : ∃ g : 𝓢(ℝ, ℂ), ∀ y > 0, 𝓕 g ((2 * π)⁻¹ * log y) = y * ψ y := by
    let k x := rexp (2 * π * x) * ψ (exp (2 * π * x))
    have hk : ContDiff ℝ ∞ k := by
      have : ContDiff ℝ ∞ fun x ↦ rexp (2 * π * x) := by fun_prop
      exact (ofRealCLM.contDiff.comp this).mul (hsmooth.comp this)
    have hk' : HasCompactSupport k := by
      have := (hsupp.comp_exp fun h₀ ↦ lt_irrefl 0 (hplus h₀)).comp_smul two_pi_pos.ne'
      simpa using! this.mul_left
    refine ⟨𝓕⁻ (hk'.toSchwartzMap hk), fun y hy ↦ ?_⟩
    simp only [fourier_fourierInv_eq, HasCompactSupport.toSchwartzMap_toFun, k]
    field_simp
    simp [exp_log hy]
  have key : ∀ᶠ x in atTop,
      remainder f A 1 (𝓕 g) x = ∑' n, f n * ψ (n / x) / x - A * ∫ y in Ioi 0, ψ y := by
    filter_upwards [eventually_gt_atTop 0, tendsto_inv_atTop_zero.eventually
      (eventually_setIntegral_Ioi_eq_of_eventuallyEq_zero (μ := volume) hψ₀)] with x hx hint
    simp only [remainder, smoothedSum, poleTerm_one, ← hint, ofReal_one]
    congr 1
    · refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [hψ₀.self_of_nhds]
      rw [hg _ (by positivity)]
      simp [term, hn, field]
    · rw [integral_Ici_eq_integral_Ioi, show x⁻¹ = rexp (-log x) by rw [Real.exp_neg, exp_log hx],
        ← integral_comp_exp_Ioi]
      exact congr(_ * $(setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ by
        rw [real_smul, ← hg _ (exp_pos u), Real.log_exp]))
  simpa [tendsto_sub_nhds_zero_iff, tsum_div_const] using
    (tendsto_remainder_one_fourier h g).congr' key

include h in
/-- A version of smoothed Wiener-Ikehara for real-valued cutoffs. -/
public lemma tendsto_sum_div_smooth_real {Ψ : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun x ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (𝓝 (A * ∫ y in Ioi 0, Ψ y)) := by
  have := (continuous_re.tendsto _).comp (tendsto_sum_div_smooth h
    (ofRealCLM.contDiff.comp hsmooth) (hsupp.comp_left rfl)
    (by rwa [tsupport, support_comp_eq]; simp))
  simp only [comp_apply, ofRealCLM_apply, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at this
  exact_mod_cast this

end Smooth

include h in
/-- The residue `A` in the Wiener-Ikehara theorem is non-negative. -/
public theorem _root_.IsWienerIkehara.A_nonneg : 0 ≤ A := by
  obtain ⟨ψ, hψ, hcs, hts, hle, -, hint, -⟩ :=
    Real.exists_contDiff_indicator_Icc_le_le_indicator_Ioo one_lt_two (by norm_num : (2 : ℝ) ≤ 3)
      (by norm_num : (3 : ℝ) < 4)
  have hts' : tsupport ψ ⊆ Ioi 0 := hts.trans fun y hy ↦ zero_lt_one.trans hy.1
  have hI : ∫ y in Ioi 0, ψ y = ∫ y, ψ y := setIntegral_eq_integral_of_forall_compl_eq_zero
    fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h' ↦ hy (hts' h')
  have hψ₀ (y : ℝ) : 0 ≤ ψ y := (indicator_nonneg (fun _ _ ↦ zero_le_one) y).trans (hle y)
  refine nonneg_of_mul_nonneg_left (ge_of_tendsto
    (tendsto_sum_div_smooth_real h hψ hcs hts') ?_) (by rw [hI]; linarith)
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact div_nonneg (tsum_nonneg fun n ↦ mul_nonneg (h.nonneg n) (hψ₀ _)) hx

include h in
lemma eventually_lt_sum_range_div {c : ℝ} (hc : c < A) :
    ∀ᶠ N : ℕ in atTop, c < (∑ i ∈ .range N, f i) / N := by
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c < A * (1 - 3 * ε) := by
    have : ContinuousWithinAt (fun ε ↦ A * (1 - 3 * ε)) (Ioi 0) 0 := by fun_prop
    exact this (Ioi_mem_nhds (by grind))
  obtain ⟨ε, hcε, hε, hε'⟩ := (hg.and (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 3))).exists
  obtain ⟨ψ, hψ, hcs, hts, -, hle, hint, -⟩ :=
    Real.exists_contDiff_indicator_Icc_le_le_indicator_Ioo (by linarith : ε < 2 * ε) (by linarith)
      (by linarith : 1 - ε < 1)
  have hts' : tsupport ψ ⊆ Ioi 0 := hts.trans fun y hy ↦ hε.trans hy.1
  have hI : ∫ y in Ioi 0, ψ y = ∫ y, ψ y := setIntegral_eq_integral_of_forall_compl_eq_zero
    fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h' ↦ hy (hts' h')
  filter_upwards [(tendsto_sum_div_smooth_real h hψ hcs hts').comp
    tendsto_natCast_atTop_atTop (Ioi_mem_nhds (by rw [hI]; nlinarith [h.A_nonneg])
    (a := c)), eventually_gt_atTop 0] with N hN _
  have hN₀ : (0 : ℝ) < N := by norm_cast
  refine hN.trans_le ?_
  simp only [comp_apply]
  grw [(hle.trans (indicator_le_indicator_of_subset (by grind : Ioo ε 1 ⊆ Ico 0 1) (by simp))) _,
    tsum_mul_indicator_Ico_natCast_div (hx := hN₀), zero_mul, one_mul, Nat.ceil_zero,
    Nat.ceil_natCast, Nat.Ico_zero_eq_range]
  exacts [h.nonneg _, hcs.summable_mul_natCast_div f hN₀.ne', (hasCompactSupport_indicator
    (isCompact_Icc.closure_of_subset Ico_subset_Icc_self)).summable_mul_natCast_div f hN₀.ne']

include h in
lemma eventually_sum_range_div_lt {c : ℝ} (hc : A < c) :
    ∀ᶠ N : ℕ in atTop, (∑ i ∈ .range N, f i) / N < c := by
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A + 2 * C * ε + ε < c := by
    have : ContinuousWithinAt (fun ε ↦ A + 2 * C * ε + ε) (Ioi 0) 0 := by fun_prop
    exact this (Iio_mem_nhds (by grind))
  obtain ⟨ε, hcε, hε, hε'⟩ := (hg.and (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
  obtain ⟨ψ, hψ, hcs, hts, hle, -, -, hint⟩ :=
    Real.exists_contDiff_indicator_Icc_le_le_indicator_Ioo (by linarith : ε < 2 * ε) (by linarith)
      (by linarith : 1 < 1 + ε)
  have hts' : tsupport ψ ⊆ Ioi 0 := hts.trans fun y hy ↦ hε.trans hy.1
  have hI : ∫ y in Ioi 0, ψ y = ∫ y, ψ y := setIntegral_eq_integral_of_forall_compl_eq_zero
    fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h' ↦ hy (hts' h')
  have hcψ : A * ∫ y in Ioi 0, ψ y < c - 2 * C * ε - ε := by
    rw [hI]
    nlinarith [h.A_nonneg]
  filter_upwards [(tendsto_sum_div_smooth_real h hψ hcs hts').comp
    tendsto_natCast_atTop_atTop (Iio_mem_nhds hcψ), eventually_gt_atTop 0,
    (tendsto_const_div_atTop_nhds_zero_nat C).eventually (gt_mem_nhds hε)] with N hN _ hN'
  have hN₀ : (0 : ℝ) < N := by norm_cast
  have hsum : ∑ i ∈ .Ico ⌈2 * ε * N⌉₊ N, f i = ∑' n, f n * indicator (Ico (2 * ε) 1) 1 (n / N) := by
    rw [tsum_mul_indicator_Ico_natCast_div (hx := hN₀), one_mul, Nat.ceil_natCast]
  grw [← Finset.sum_range_add_sum_Ico _ (by rw [Nat.ceil_le]; nlinarith : ⌈2 * ε * N⌉₊ ≤ N),
    add_div, hsum, ((indicator_le_indicator_of_subset Ico_subset_Icc_self
    (by simp)).trans hle) _, (by exact hN : (∑' n, f n * ψ (n / N)) / N < _),
    h.sum_range_le, Nat.ceil_lt_add_one, mul_add, add_div, mul_one, hN']
  · field_simp
    grind
  · exact h.C_nonneg
  · positivity
  exacts [h.nonneg _, (hasCompactSupport_indicator
    (isCompact_Icc.closure_of_subset Ico_subset_Icc_self)).summable_mul_natCast_div f hN₀.ne',
    hcs.summable_mul_natCast_div f hN₀.ne']

include h in
/-- The *Wiener-Ikehara Tauberian Theorem*, summing over naturals `n < N`; see
`WienerIkehara.tendsto_sum_div` for the version summing over reals `n ≤ x`. -/
public theorem tendsto_sum_range_div : Tendsto (fun N ↦ (∑ i ∈ .range N, f i) / N) atTop (𝓝 A) :=
  tendsto_order.mpr ⟨fun _ ↦ eventually_lt_sum_range_div h, fun _ ↦ eventually_sum_range_div_lt h⟩

include h in
/-- The *Wiener-Ikehara Tauberian Theorem*, summing over naturals `n ≤ x` for real `x`; see
`WienerIkehara.tendsto_sum_range_div` for the version summing over naturals `n < N`. -/
public theorem tendsto_sum_div : Tendsto (fun x ↦ (∑ n ∈ .Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A) := by
  have : Tendsto (fun x ↦ (∑ i ∈ .range (⌊x⌋₊ + 1), f i) / (⌊x⌋₊ + 1) * ((⌊x⌋₊ + 1) / x)) atTop
      (𝓝 A) := by
    rw [← mul_one A]
    apply Tendsto.mul
    · simpa [Function.comp_def] using (tendsto_sum_range_div h).comp
        ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    · convert (tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero <;> grind
  apply this.congr'
  filter_upwards [eventually_gt_atTop 0] with x
  have : (⌊x⌋₊ : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.range_eq_Icc_zero_sub_one _ (by lia)]
  simp [field]

end WienerIkehara

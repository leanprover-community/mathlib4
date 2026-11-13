/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.NumberTheory.LSeries.Basic

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Group.Circle
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The Wiener-Ikehara Tauberian theorem

Let `f : ℕ → ℝ` be non-negative with `∑ n ≤ x, f n ≪ x`, whose `L`-series `F` extends
continuously to `Re s ≥ 1` after subtracting `A / (s - 1)`.  Then
`∑ n < N, f n = A * N + o(N)`.

The classical theorem does not need the bound `∑ n ≤ x, f n ≪ x`, only the convergence of `F(s)`
for `Re s > 1` (which the bound implies); it is assumed here because it simplifies the proof.

## Main results

* `WienerIkehara.tendsto_sum_div`, `WienerIkehara.tendsto_sum_range_div`: the Wiener-Ikehara
Tauberian theorem, summing over reals `n ≤ x` and over naturals `n < N` respectively.
* `WienerIkehara.tendsto_sum_div_smooth`, `WienerIkehara.tendsto_sum_div_smooth_real`: versions
for smooth cutoffs.

## Proof outline

Writing `ψ̂` for the Fourier transform, the proof studies `S f A σ ψ̂ x`, the difference
between `∑' n, term f σ n * ψ̂ (log (n / x) / (2 * π))` and its polar counterpart.  Rewriting both
halves as Fourier integrals (`sum_term_mul_fourier_eq`, `integral_exp_mul_fourier_eq`) cancels the
pole and expresses `S` through `G` (`sum_term_mul_sub_mul_integral_eq`); letting `σ → 1`
and applying the Riemann-Lebesgue lemma gives `S f A 1 ψ̂ x → 0`, first for compactly supported
test functions (`tendsto_S_one_fourier_of_hasCompactSupport`) and then for all Schwartz
functions (`tendsto_S_one_fourier`).
Surjectivity of the Fourier transform on Schwartz space upgrades this to a smoothed form of the
theorem (`tendsto_sum_div_smooth_real`), and non-negativity of `f` together with a smooth Urysohn
lemma (`exists_cutoff`) replaces the smooth cutoff by the indicator of
an interval, whence the theorem (`tendsto_sum_div`).

This file is adapted from the `PrimeNumberTheoremAnd` project.
-/

public noncomputable section

open Complex hiding log
open Real MeasureTheory Filter Set FourierTransform LSeries Asymptotics SchwartzMap
  Function
open scoped Topology ContDiff ComplexConjugate LSeries.notation

namespace SchwartzMap

variable (ψ : 𝓢(ℝ, ℂ)) (u : ℝ)

/-- In the arguments of this file, it is convenient to isolate a bespoke seminorm for
Schwartz functions that controls the decay of their Fourier transform. -/
private def Q : ℝ := (𝓕 ψ).seminorm ℝ 0 0 + (𝓕 ψ).seminorm ℝ 2 0

private lemma Q_nonneg : 0 ≤ ψ.Q := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

private lemma continuous_Q : Continuous Q :=
  (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp (by fun_prop)).add
    (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2, 0)).comp (by fun_prop))

private lemma norm_fourier_le_Q_mul : ‖𝓕 ψ u‖ ≤ ψ.Q * (1 + u ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2), Q]
  have h := norm_pow_mul_le_seminorm ℝ (𝓕 ψ) 2 u
  rw [Real.norm_eq_abs, sq_abs] at h
  linarith [norm_le_seminorm ℝ (𝓕 ψ) u]

end SchwartzMap

namespace WienerIkehara

variable (f : ℕ → ℝ) (A : ℝ) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ)

private abbrev c₀ := π⁻¹ * 2⁻¹

private def S₁ : ℂ := ∑' n, term ↗f σ n * φ (c₀ * log (n / x))

private def S₂ : ℂ := A * ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x), rexp (-u * (σ - 1)) * φ (c₀ * u)

/-- A key statistic in the Wiener--Ikehara analysis involving an exponent `σ`, a test
function `φ`, and a scale parameter `x`. -/
private def S : ℂ := S₁ f σ φ x - S₂ A σ φ x

private lemma S₂_one : S₂ A 1 φ x = A * ∫ u in Ici (-log x), φ (c₀ * u) := by
  simp [S₂]

/- The data and hypotheses for the Wiener-Ikehara theorem, supplied as individual hypotheses:
a nonnegative function `f` (`hpos`) obeying a Chebyshev-type bound with constant `C` (`bound`),
an asymptotic constant `A`, and a continuous extension `G` of `s ↦ LSeries f s - A / (s - 1)`
to `re s ≥ 1` (`hG`, `hG'`). -/
variable {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ} (bound : ∀ n, ∑ i ∈ .range n, f i ≤ C * n)
  (hG : ContinuousOn G {s | 1 ≤ s.re})
  (hG' : EqOn G (fun s ↦ LSeries ↗f s - A / (s - 1)) {s | 1 < s.re}) (hpos : 0 ≤ f)

include bound hpos in
private lemma C_nonneg : 0 ≤ C := (hpos 0).trans (by simpa using bound 1)

section FourierIdentities

variable {x σ : ℝ} (ψ : 𝓢(ℝ, ℂ)) (hx : 0 < x) (hσ : 1 < σ)

include hpos bound hσ in
private lemma lSeriesSummable : LSeriesSummable ↗f (σ : ℂ) := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ hpos zero_le_one (by simpa)
  refine isBigO_of_le' (c := 2 * C) _ fun n ↦ ?_
  rw [norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ hpos k), rpow_one, Real.norm_natCast]
  calc
    _ ≤ ∑ k ∈ .range (2 * n), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg (by grind) fun k _ _ ↦ hpos k
    _ ≤ _ := (bound (2 * n)).trans_eq (by push_cast; ring)

include hx in
private lemma fourierChar_neg_mul_log_div {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (𝐞 (-(c₀ * log (n / x) * t)) : ℂ) = x ^ (t * I) / n ^ (t * I) := by
  simp [fourierChar_apply, cpow_def_of_ne_zero, hx.ne', hn, ← Complex.exp_sub, log_div,
    ofReal_log, hx.le]
  congr
  field

include bound hpos hx hσ in
private lemma sum_term_mul_fourier_eq :
    S₁ f σ (𝓕 ψ) x = ∫ t : ℝ, LSeries ↗f (σ + t * I) * ψ t * x ^ (t * I) :=
  calc
    _ = ∑' n, ∫ t, term ↗f σ n * 𝐞 (-(c₀ * log (n / x) * t)) • ψ t := by
      simp [S₁, fourier_coe, fourier_eq, integral_const_mul]
    _ = ∫ t, ∑' n, _ := by
      refine integral_tsum_of_summable_integral_norm (fun n ↦ ?_) ?_
      · exact (ψ.integrable.norm.const_mul ‖term ↗f σ n‖).mono' (by fun_prop)
          (.of_forall fun t ↦ by simp)
      · simpa [integral_const_mul] using
          (lSeriesSummable bound hpos hσ).norm.mul_right (∫ t, ‖ψ t‖)
    _ = _ := by
      congr with t
      rw [LSeries, mul_assoc, ← tsum_mul_right]
      congr with n
      by_cases hn : n = 0
      · simp [*]
      rw [Circle.smul_def, fourierChar_neg_mul_log_div hx hn]
      simp [cpow_add, field, *]

include hx hσ in
private lemma mul_integral_exp_mul_fourierChar_eq (t : ℝ) :
    ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x), (rexp (-u * (σ - 1)) : ℂ) * 𝐞 (-(t * (c₀ * u))) =
      x ^ (t * I) / (σ + t * I - 1) := by
  have : ∫ u in Ici (-log x), (rexp (-u * (σ - 1)) : ℂ) * 𝐞 (-(t * (c₀ * u))) =
      ∫ u in Ioi (-log x), cexp (-(σ - 1 + t * I) * u) := by
    rw [integral_Ici_eq_integral_Ioi]
    congr with u
    push_cast [fourierChar_apply, ← Complex.exp_add]
    congr 1
    field
  rw [this, integral_cexp_neg_mul_Ioi_neg_log hx (by simpa using hσ), ofReal_cpow hx.le,
    mul_div_assoc', ← cpow_add _ _ (mod_cast hx.ne')]
  push_cast
  ring_nf

include hx hσ in
private lemma integral_exp_mul_fourier_eq :
    S₂ A σ (𝓕 ψ) x = A * ∫ t, (1 / (σ + t * I - 1)) * ψ t * x ^ (t * I) := by
  have hint : IntegrableOn (fun u ↦ rexp (-u * (σ - 1))) (Ici (-log x)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    convert exp_neg_integrableOn_Ioi (-log x) (sub_pos.mpr hσ) using 1
    ext u; ring_nf
  rw [S₂, mul_assoc]; congr 1
  calc
  _ = ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x),
      ∫ t, (rexp (-u * (σ - 1)) : ℂ) • 𝐞 (-(t * (c₀ * u))) • ψ t := by
    simp_rw [fourier_coe, fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  _ = ↑(x ^ (1 - σ)) * ∫ t, ∫ u in Ici (-log x), _ :=
    congr(_ * $(integral_integral_swap ((Integrable.mul_prod hint ψ.integrable.norm).mono'
      (by fun_prop) (.of_forall fun ⟨u, t⟩ ↦ by simp [Complex.norm_exp]))))
  _ = _ := by
    rw [← integral_const_mul]
    congr with t
    simp_rw [Circle.smul_def, smul_smul, smul_eq_mul, integral_mul_const]
    rw [← mul_assoc, mul_integral_exp_mul_fourierChar_eq hx hσ]
    ring

include hx in
private lemma continuous_cpow_mul_I : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
  continuous_const.cpow (by fun_prop) (by simp [hx])

include bound hpos hG hG' hx in
/-- The main result of this section: an initial Fourier identity expressing a sum of
`f` as an error term of Fourier integral type. -/
private lemma sum_term_mul_sub_mul_integral_eq {ψ : 𝓢(ℝ, ℂ)} (hψ : HasCompactSupport ψ)
    {σ : ℝ} (hσ : 1 < σ) : S f A σ (𝓕 ψ) x = ∫ t : ℝ, G (σ + t * I) * ψ t * x ^ (t * I) := by
  have hσt (t : ℝ) : 1 < (σ + t * I).re := by simpa using hσ
  have (t : ℝ) : (σ : ℂ) + t * I - 1 ≠ 0 := ne_zero_of_re_pos (by simpa using hσ)
  have hcpow := continuous_cpow_mul_I hx
  have hGc : Continuous fun t : ℝ ↦ G (σ + t * I) :=
    hG.comp_continuous (by fun_prop) fun t ↦ (hσt t).le
  have hint₁ : Integrable fun t : ℝ ↦ G (σ + t * I) * ψ t * x ^ (t * I) :=
    ((hGc.mul ψ.continuous).mul hcpow).integrable_of_hasCompactSupport hψ.mul_left.mul_right
  have hint₂ : Integrable fun t : ℝ ↦ A * (1 / (σ + t * I - 1) * ψ t * x ^ (t * I)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ.mul_left.mul_right.mul_left
  rw [S, sum_term_mul_fourier_eq bound hpos ψ hx hσ, integral_exp_mul_fourier_eq ψ hx hσ,
    sub_eq_iff_eq_add, ← integral_const_mul, ← integral_add hint₁ hint₂]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [hG' (hσt t)]
  ring

end FourierIdentities

section Weight

variable {a c t x : ℝ} {n : ℕ}

/-- A weight function appearing in the analysis. -/
private def w (t : ℝ) : ℝ := (t * (1 + (c₀ * log t) ^ 2))⁻¹

private lemma w_nonneg (ht : 0 ≤ t) : 0 ≤ w t := by rw [w]; positivity

private lemma hasDerivAt_w (ht : t ≠ 0) : HasDerivAt w
    (- (c₀ ^ 2 * (log t + 1) ^ 2 + (1 - c₀) * (1 + c₀)) * w t ^ 2) t := by
  have : HasDerivAt (fun t ↦ t * (1 + (c₀ * log t) ^ 2))
      (1 + 2 * c₀ ^ 2 * log t + (c₀ * log t) ^ 2) t := by
    convert (hasDerivAt_id' t).mul ?_ (d' := 2 * c₀ ^ 2 * t⁻¹ * log t) using 1
    · grind
    convert (((hasDerivAt_log ht).const_mul _).pow (f' := c₀ * t⁻¹) 2).const_add _ using 1
    ring
  unfold w
  convert this.inv (by positivity) using 1
  grind

private lemma antitoneOn_w : AntitoneOn w (Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
    (fun _ _ ↦ (hasDerivAt_w (by grind)).continuousAt.continuousWithinAt)
    (fun _ _ ↦ (hasDerivAt_w (fun _ ↦ by simp_all)).hasDerivWithinAt)
    fun x _ ↦ ?_
  have : 0 < c₀ ^ 2 * (log x + 1) ^ 2 + (1 - c₀) * (1 + c₀) := by
    have : π⁻¹ ≤ 2⁻¹ := by simp [field, two_le_pi]
    positivity [(by nlinarith : 0 < 1 - π⁻¹ * 2⁻¹)]
  simp only [neg_mul, Left.neg_nonpos_iff]
  positivity

private lemma integrableOn_mul_w_div (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * w (t / c)) (Ici 0) := by
  have (t) (ht : 0 < t) : t⁻¹ • (a * c * (1 + (c₀ * (log t - log c)) ^ 2)⁻¹) = a * w (t / c)
      := by
    have : 0 < 1 + (c₀ * (log t - log c)) ^ 2 := by positivity
    simp [w, log_div ht.ne' hc.ne', field]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact ((integrableOn_comp_log_Ioi_zero _).2
    (((integrable_inv_one_add_mul_sq (by positivity)).comp_sub_right _).const_mul _)).congr_fun
    this measurableSet_Ioi

private lemma antitoneOn_inv_mul_w_div (hx : 0 < x) :
    AntitoneOn (fun t ↦ x⁻¹ * w (t / x)) (Ioc 0 n) := by
  intro u ⟨_, _⟩ v ⟨_, _⟩ huv
  apply mul_le_mul le_rfl ?_ (w_nonneg (by positivity)) (by positivity)
  exact antitoneOn_w (by rw [mem_Ioi]; positivity) (by rw [mem_Ioi]; positivity) (by grw [huv])

private lemma integrableOn_inv_mul_w_div (hx : 0 < x) :
    IntegrableOn (fun t ↦ x⁻¹ * w (t / x)) (Icc 0 n) :=
  .mono_set (integrableOn_mul_w_div (by positivity)) Icc_subset_Ici_self

private lemma inv_mul_w_div (hx : x ≠ 0) (t : ℝ) :
    x⁻¹ * w (t / x) = (t * (1 + (c₀ * log (t / x)) ^ 2))⁻¹ := by
  rw [w, ← mul_inv, ← mul_assoc, mul_div_cancel₀ t hx]

private lemma inv_mul_w_div_le_one (hx : x ≠ 0) (ht : 1 ≤ t) : x⁻¹ * w (t / x) ≤ 1 := by
  rw [inv_mul_w_div hx]
  exact inv_le_one_of_one_le₀ <| one_le_mul_of_one_le_of_one_le ht <|
    le_add_of_nonneg_right (sq_nonneg _)

private lemma antitone_ite_w (hx : 0 < x) :
    Antitone fun i : ℕ ↦ if i = 0 then (1 : ℝ) else x⁻¹ * w (i / x) := by
  intro i j hij
  rcases eq_or_ne j 0 with rfl | hj
  · simp [Nat.le_zero.mp hij]
  simp only [hj, ↓reduceIte]
  split_ifs with hi
  · exact inv_mul_w_div_le_one hx.ne' (mod_cast Nat.one_le_iff_ne_zero.mpr hj)
  · gcongr
    exact antitoneOn_w (by rw [mem_Ioi]; positivity) (by rw [mem_Ioi]; positivity) (by gcongr)

end Weight

section LimitingFourierIdentity

private lemma tendsto_integral_mul_cpow_mul_I {ψ : ℝ → ℂ} :
    Tendsto (fun x : ℝ ↦ ∫ t, ψ t * x ^ (t * I)) atTop (𝓝 0) := by
  have : ∀ᶠ x : ℝ in atTop, ∫ t, ψ t * x ^ (t * I) = ∫ t, ψ t * exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx'
    refine integral_congr_ae (Eventually.of_forall fun _ ↦ ?_)
    simp [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx', mul_assoc]
  simp_rw [tendsto_congr' this]
  convert_to Tendsto (fun x ↦ 𝓕 ψ (-c₀ * log x)) atTop (𝓝 0)
  · ext; congr with _
    simp only [← ofReal_mul, mul_comm (ψ _), fourierChar, Circle.exp,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg]
    congr; field
  exact (zero_at_infty_fourier ψ).comp <| Tendsto.mono_right
    (tendsto_log_atTop.const_mul_atTop_of_neg (by simp [pi_pos])) atBot_le_cocompact

private abbrev C₀ := 1 + ∫ t in Ioi 0, w t

private lemma C₀_nonneg : 0 ≤ C₀ :=
  add_nonneg zero_le_one (setIntegral_nonneg measurableSet_Ioi (by grind [w_nonneg]))

variable {x : ℝ} (Ψ : 𝓢(ℝ, ℂ)) (hΨ : HasCompactSupport Ψ) (hx : 1 ≤ x) (n : ℕ)

include hx in
private lemma sum_range_ite_w_le :
    ∑ i ∈ .range n, (if i = 0 then 1 else x⁻¹ * w (i / x)) ≤ 1 + ∫ t in Ioi 0, w t := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rcases n with _ | m
  · simpa using C₀_nonneg
  simp only [Finset.sum_range_succ', Nat.add_one_ne_zero, ↓reduceIte]
  rw [add_comm _ (1 : ℝ)]
  gcongr
  calc
    _ ≤ ∫ t in 0..m, x⁻¹ * w (t / x) := by
      simpa using @AntitoneOn.sum_le_integral_of_integrableOn 0 m (fun t ↦ x⁻¹ * w (t / x))
        (by simpa using antitoneOn_inv_mul_w_div hx₀)
        (by simpa using integrableOn_inv_mul_w_div hx₀)
    _ = ∫ t in 0..m / x, w t := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div w hx₀.ne',
        zero_div, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hx₀.ne', one_mul]
    _ ≤ ∫ t in Ioi 0, w t := by
      rw [intervalIntegral.integral_of_le (by positivity)]
      exact setIntegral_mono_set
        (by simpa using (integrableOn_mul_w_div (a := 1) zero_lt_one).mono_set Ioi_subset_Ici_self)
        (eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun t ht ↦ w_nonneg ht.le)
        Ioc_subset_Ioi_self.eventuallySubset

include bound hpos hx in
private lemma bound_sum_log_range :
    ∑ i ∈ .range n, ‖f i‖ / i * (1 + (c₀ * log (i / x)) ^ 2)⁻¹ ≤ C * C₀ := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have := C_nonneg bound hpos
  calc
    _ ≤ ∑ i ∈ .range n, ‖f i‖ * (if i = 0 then 1 else x⁻¹ * w (i / x)) := by
      gcongr 1 with i
      by_cases i = 0 <;> simp [*, w, field]
    _ ≤ ∑ i ∈ .range n, C * (if i = 0 then 1 else x⁻¹ * w (i / x)) :=
      Finset.sum_mul_le_sum_mul_of_sum_range_le
        (fun k _ ↦ by simpa [mul_comm, Real.norm_of_nonneg (hpos _)] using bound k)
        (fun i ↦ by
          simp only [Pi.zero_apply]
          split_ifs
          exacts [zero_le_one, mul_nonneg (by positivity) (w_nonneg (by positivity))])
        ((antitone_ite_w hx₀).antitoneOn _)
    _ ≤ C * C₀ := by
      rw [← Finset.mul_sum]
      gcongr
      exact sum_range_ite_w_le hx n

include bound hpos hx in
private lemma summable_sum_log_range :
    Summable fun n ↦ ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ := summable_of_sum_range_le
  (fun _ ↦ by positivity) (fun n ↦ by simpa using bound_sum_log_range bound hpos hx n)

private lemma norm_term_mul_le (x : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ ≤
    Ψ.Q * (‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹) := by
  convert mul_le_mul_of_nonneg_left (Ψ.norm_fourier_le_Q_mul (1 / (2 * π) * log (n / x)))
    (norm_nonneg (f n / n)) using 1
  · simp [term_of_ne_zero']
  · simp; grind

include bound hpos hx in
private theorem tendsto_S₁ : Tendsto (S₁ f · (𝓕 Ψ) x) (𝓝[>] 1) (𝓝 (S₁ f 1 (𝓕 Ψ) x)) := by
  simp only [S₁]
  refine tendsto_tsum_of_dominated_convergence
    ((summable_sum_log_range bound hpos hx).mul_left Ψ.Q) (fun n ↦ ?_) ?_
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
private theorem tendsto_S₂ : Tendsto (S₂ A · (𝓕 Ψ) x) (𝓝[>] 1) (𝓝 (S₂ A 1 (𝓕 Ψ) x)) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  apply Tendsto.mul
  · exact (Continuous.tendsto (by fun_prop (disch := simp [hx₀.ne'])) 1).mono_left
      nhdsWithin_le_nhds
  refine tendsto_integral_filter_of_dominated_convergence (fun t ↦ x * ‖𝓕 Ψ (c₀ * t)‖)
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

include hG hΨ hx in
private theorem tendsto_integral_G_mul :
    Tendsto (fun σ : ℝ ↦ ∫ t : ℝ, G (σ + t * I) * Ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * Ψ t * x ^ (t * I))) := by
  have hcpow := continuous_cpow_mul_I (zero_lt_one.trans_le hx)
  have hGc : Continuous fun p : ℝ × ℝ ↦ G (max p.1 1 + p.2 * I) :=
    hG.comp_continuous (by fun_prop) fun p ↦ by simp
  have hF : Continuous (uncurry fun σ t : ℝ ↦ G (max σ 1 + t * I) * Ψ t * x ^ (t * I)) :=
    (hGc.mul (Ψ.continuous.comp continuous_snd)).mul (hcpow.comp continuous_snd)
  have hI (σ : ℝ) : ∫ (t : ℝ) in tsupport Ψ, G (max σ 1 + t * I) * Ψ t * x ^ (t * I) =
      ∫ t : ℝ, G (max σ 1 + t * I) * Ψ t * x ^ (t * I) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by
      simp [image_eq_zero_of_notMem_tsupport ht]
  have := (continuous_parametric_integral_of_continuous (μ := volume) hF hΨ).tendsto 1
  simp only [hI] at this
  simp only [max_self, ofReal_one] at this
  refine (this.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  simp only [max_eq_left hσ.le]

include bound hG hG' hpos hΨ in
private lemma tendsto_S_one_fourier_of_hasCompactSupport :
    Tendsto (S f A 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  apply (tendsto_integral_mul_cpow_mul_I (ψ := fun t ↦ G (1 + t * I) * (Ψ t))).congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [S]
  apply (tendsto_nhds_unique_of_eventuallyEq ((tendsto_S₁ bound hpos Ψ hx).sub (tendsto_S₂ Ψ hx))
    (tendsto_integral_G_mul hG Ψ hΨ hx) _).symm
  exact (eventuallyEq_nhdsWithin_iff.mpr (.of_forall fun σ hσ ↦
    sum_term_mul_sub_mul_integral_eq bound hG hG' hpos (by linarith) hΨ hσ))

end LimitingFourierIdentity

section LimitingFourierIdentitySchwartz

variable (Ψ φ φ' : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : 1 ≤ x)

private lemma norm_setIntegral_fourier_le (x : ℝ) :
    ‖∫ u in Ici (-log x), 𝓕 Ψ (c₀ * u)‖ ≤ Ψ.Q * ∫ u, (1 + (c₀ * u) ^ 2)⁻¹ := by
  have hint : Integrable fun u : ℝ ↦ Ψ.Q * (1 + (c₀ * u) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' (by positivity)).const_mul _
  rw [← integral_const_mul]
  exact (norm_integral_le_of_norm_le hint.integrableOn
    (.of_forall fun u ↦ Ψ.norm_fourier_le_Q_mul _)).trans
    (setIntegral_le_integral hint (.of_forall fun _ ↦ mul_nonneg Ψ.Q_nonneg (by positivity)))

include bound hpos hx in
private lemma summable_term_mul : Summable fun n ↦ ‖(term ↗f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_mul_le Ψ x ↗f)
    (by simpa using (summable_sum_log_range bound hpos hx).const_smul Ψ.Q)

include bound hpos hx in
/-- The map `φ ↦ S f A 1 (𝓕 φ) x` is linear in the test function. -/
private lemma S_one_sub : S f A 1 (𝓕 (φ - φ')) x = S f A 1 (𝓕 φ) x - S f A 1 (𝓕 φ') x := by
  have hs (ψ : 𝓢(ℝ, ℂ)) := (summable_term_mul bound hpos ψ hx).of_norm
  have hi (ψ : 𝓢(ℝ, ℂ)) : IntegrableOn (fun u ↦ 𝓕 ψ (c₀ * u)) (Ici (-log x)) :=
    ((𝓕 ψ).integrable.comp_mul_left' (by positivity)).integrableOn
  simp only [S, S₁, S₂_one, fourier_sub, sub_apply, mul_sub, ofReal_one]
  rw [Summable.tsum_sub (hs φ) (hs φ'), integral_sub (hi φ) (hi φ')]
  ring

include bound hpos in
/-- `φ ↦ S f A 1 (𝓕 φ) x` is bounded by a multiple of the seminorm `φ.Q`, uniformly in `x ≥ 1`. -/
private lemma exists_norm_S_one_le :
    ∃ K, ∀ (φ : 𝓢(ℝ, ℂ)) {x : ℝ}, 1 ≤ x → ‖S f A 1 (𝓕 φ) x‖ ≤ φ.Q * K := by
  refine ⟨C * C₀ + |A| * ∫ u, (1 + (c₀ * u) ^ 2)⁻¹, fun φ x hx ↦ ?_⟩
  have h₁ : ‖S₁ f 1 (𝓕 φ) x‖ ≤ φ.Q * (C * C₀) := by
    rw [S₁, ofReal_one]
    refine (norm_tsum_le_tsum_norm (summable_term_mul bound hpos φ hx)).trans ?_
    calc
      _ ≤ ∑' n, φ.Q * (‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹) :=
        (summable_term_mul bound hpos φ hx).tsum_mono
          ((summable_sum_log_range bound hpos hx).mul_left _)
          fun n ↦ (norm_term_mul_le φ x ↗f n).trans_eq (by simp)
      _ ≤ _ := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (tsum_le_of_sum_range_le (fun _ ↦ by positivity)
          (bound_sum_log_range bound hpos hx)) φ.Q_nonneg
  have h₂ : ‖S₂ A 1 (𝓕 φ) x‖ ≤ φ.Q * (|A| * ∫ u, (1 + (c₀ * u) ^ 2)⁻¹) := by
    simp only [S₂_one, norm_mul, norm_real, norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (norm_setIntegral_fourier_le φ x) (abs_nonneg A)).trans_eq
      (by ring)
  rw [S]
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (mul_add ..).symm)

include bound hG hG' hpos in
private lemma tendsto_S_one_fourier : Tendsto (S f A 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_norm_S_one_le (A := A) bound hpos
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨φ, hφQ : _ < ε / 2, hφcs⟩ := SchwartzMap.dense_hasCompactSupport.inter_open_nonempty
    {φ | (Ψ - φ).Q * K < ε / 2}
    (isOpen_lt ((SchwartzMap.continuous_Q.comp (by fun_prop)).mul continuous_const)
      continuous_const)
    ⟨Ψ, by simpa [Q] using half_pos hε⟩
  filter_upwards [eventually_ge_atTop 1, Metric.tendsto_nhds.mp
    (tendsto_S_one_fourier_of_hasCompactSupport bound hG hG' hpos φ hφcs) (ε / 2)
    (half_pos hε)] with x hx hφ
  rw [dist_zero_right] at hφ ⊢
  calc
    _ = ‖S f A 1 (𝓕 (Ψ - φ)) x + S f A 1 (𝓕 φ) x‖ := by
      rw [S_one_sub bound hpos Ψ φ hx, sub_add_cancel]
    _ < _ := by grw [norm_add_le, hφ, hK (Ψ - φ) hx, hφQ]; grind

end LimitingFourierIdentitySchwartz

section Smooth

variable {ψ : ℝ → ℂ} (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (hplus : tsupport ψ ⊆ Ioi 0)

include hplus in
private lemma eventually_eq_zero_of_tsupport_subset : ∀ᶠ x in 𝓝 0, ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ lt_irrefl 0 <| mem_Ioi.mp (hplus h))

include hsupp hplus in
private theorem hasCompactSupport_comp_exp : HasCompactSupport (ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp ⊢
  exact ⟨tendsto_exp_atBot <| eventually_eq_zero_of_tsupport_subset hplus,
    tendsto_exp_atTop hsupp.2⟩

/-- If `ψ` vanishes near `0`, then eventually `∫ y in Ioi x⁻¹, ψ y = ∫ y in Ioi 0, ψ y`. -/
private lemma eventually_setIntegral_Ioi_inv_eq (hψ : ∀ᶠ x in 𝓝 0, ψ x = 0) :
    ∀ᶠ x : ℝ in atTop, ∫ y in Ioi x⁻¹, ψ y = ∫ y in Ioi 0, ψ y := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hψ
  filter_upwards [eventually_gt_atTop ε⁻¹] with x hx
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (inv_pos.mpr ((inv_pos.mpr hε).trans hx)).le) fun y ⟨hy, hy'⟩ ↦ h ?_).symm
  grw [Real.dist_eq, sub_zero, abs_of_pos hy, not_lt.mp hy', inv_lt_of_inv_lt₀ hε hx]

include hsmooth hsupp hplus in
/-- `y ↦ y * ψ y`, written in the variable `c₀ * log y`, is a Fourier transform. -/
private lemma exists_fourier_eq : ∃ g : 𝓢(ℝ, ℂ), ∀ y > 0, 𝓕 g (c₀ * log y) = y * ψ y := by
  let h x := rexp (2 * π * x) * ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ fun x ↦ rexp (2 * π * x) := (contDiff_const.mul contDiff_id).exp
    exact (ofRealCLM.contDiff.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    simpa using! (hasCompactSupport_comp_exp hsupp hplus).comp_smul two_pi_pos.ne' |>.mul_left
  refine ⟨𝓕⁻ (h2.toSchwartzMap h1), fun y hy ↦ ?_⟩
  simp only [fourier_fourierInv_eq, HasCompactSupport.toSchwartzMap_toFun, h]
  field_simp
  rw [exp_log hy]

include bound hG hG' hpos hsmooth hsupp hplus in
/-- A smoothed *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function with `∑ i < n, f i ≤ C * n` whose L-series has a simple pole at `s = 1` with residue `A`
and otherwise extends continuously to the closed half-plane `re s ≥ 1`, then `f` behaves like `A`
asymptotically with respect to smooth weights with compact support in `(0, ∞)`. -/
lemma tendsto_sum_div_smooth : Tendsto (fun x ↦ (∑' n, f n * ψ (n / x)) / x)
    atTop (𝓝 (A * ∫ y in Ioi 0, ψ y)) := by
  obtain ⟨g, hg⟩ := exists_fourier_eq hsmooth hsupp hplus
  have h3 : ∀ᶠ x in atTop,
      S f A 1 (𝓕 g) x = ∑' n, f n * ψ (n / x) / x - A * ∫ y in Ioi 0, ψ y := by
    filter_upwards [eventually_gt_atTop 0, eventually_setIntegral_Ioi_inv_eq
      (eventually_eq_zero_of_tsupport_subset hplus)] with x hx hint
    simp only [S, S₁, S₂_one, ← hint, ofReal_one]
    congr 1
    · refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [(eventually_eq_zero_of_tsupport_subset hplus).self_of_nhds]
      rw [hg _ (by positivity)]
      simp [term, hn, field]
    · rw [integral_Ici_eq_integral_Ioi, show x⁻¹ = rexp (-log x) by rw [Real.exp_neg, exp_log hx],
        ← integral_comp_exp_Ioi]
      exact congr(_ * $(setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ by
        rw [real_smul, ← hg _ (exp_pos u), Real.log_exp]))
  simpa [tendsto_sub_nhds_zero_iff, tsum_div_const] using
    (tendsto_S_one_fourier bound hG hG' hpos g).congr' h3

include bound hG hG' hpos in
/-- A version of smoothed Wiener-Ikehara for real-valued cutoffs. -/
lemma tendsto_sum_div_smooth_real {Ψ : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun x ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (𝓝 (A * ∫ y in Ioi 0, Ψ y)) := by
  have := (continuous_re.tendsto _).comp (tendsto_sum_div_smooth bound hG hG' hpos
      (ofRealCLM.contDiff.comp hsmooth) (hsupp.comp_left rfl)
      (by rwa [tsupport, support_comp_eq]; simp))
  simp at this; norm_cast at this

end Smooth

/-- A smooth Urysohn lemma for cutoffs supported away from the
origin, additionally controlling the integral of the cutoff from above and below by the lengths of
`Ioo a d` and `Icc b c` respectively. -/
private lemma exists_cutoff {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∃ ψ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧
      indicator (Icc b c) 1 ≤ ψ ∧ ψ ≤ indicator (Ioo a d) 1 ∧
      c - b ≤ ∫ y in Ioi 0, ψ y ∧ ∫ y in Ioi 0, ψ y ≤ d - a := by
  obtain ⟨ψ, h1, h2, h3, h4⟩ := exists_contDiff_support_eq_eq_one_iff
    isOpen_Ioo isClosed_Icc (Icc_subset_Ioo hab hcd)
  have h5 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (h3 ▸ Ioo_subset_Icc_self)
  have h6 := indicator_le' (fun x hx ↦ ((h4 x).mp hx).ge) fun x _ ↦ (h2 (mem_range_self x)).1
  have h7 : ψ ≤ indicator (Ioo a d) 1 := fun x ↦ le_indicator_apply
    (fun _ ↦ (h2 (mem_range_self x)).2) (by grind)
  have h8 : tsupport ψ ⊆ Ioi 0 := by grind [tsupport, closure_Ioo]
  have h9 : Integrable ψ := h1.continuous.integrable_of_hasCompactSupport h5
  have h10 : ∫ y in Ioi 0, ψ y = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      notMem_support.1 fun h ↦ hx (h8 (subset_tsupport _ h))
  have h11 {s} (hs : MeasurableSet s) (hs' : volume s ≠ ⊤) : Integrable (indicator s (1 : ℝ → ℝ))
    := (integrable_indicator_iff hs).2 (integrableOn_const hs' (by simp))
  refine ⟨ψ, h1, h5, h8, h6, h7, ?_, ?_⟩
  · rw [h10, ← volume_real_Icc_of_le hbc, ← integral_indicator_one measurableSet_Icc]
    exact integral_mono (h11 measurableSet_Icc (by simp)) h9 h6
  · rw [h10, ← volume_real_Ioo_of_le (by order), ← integral_indicator_one measurableSet_Ioo]
    exact integral_mono h9 (h11 measurableSet_Ioo (by simp)) h7

include hpos bound hG hG' in
private lemma A_nonneg : 0 ≤ A := by
  obtain ⟨ψ, h1, h2, h3, h4, -, h6, -⟩ :=
    exists_cutoff one_pos one_lt_two (by norm_num : (2 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) < 4)
  have hψ (y : ℝ) : 0 ≤ ψ y := (indicator_nonneg (fun _ _ ↦ zero_le_one) y).trans (h4 y)
  refine nonneg_of_mul_nonneg_left (ge_of_tendsto
    (tendsto_sum_div_smooth_real bound hG hG' hpos h1 h2 h3) ?_) (by linarith)
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact div_nonneg (tsum_nonneg fun n ↦ mul_nonneg (hpos n) (hψ _)) hx

private lemma summable_mul {x : ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable fun n ↦ f n * g (n / x) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  simp only [HasFiniteSupport, support_mul]
  apply Finite.inter_of_right
  rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi ↦ by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

private lemma hasCompactSupport_indicator_Ico (u v : ℝ) :
    HasCompactSupport (indicator (Ico u v) (1 : ℝ → ℝ)) :=
  .of_support_subset_isCompact isCompact_Icc (support_indicator_subset.trans Ico_subset_Icc_self)

private lemma tsum_mul_indicator_Ico {N : ℕ} (hN : (0 : ℝ) < N) (u : ℝ) :
    ∑' n, f n * (indicator (Ico u 1) 1 (n / N)) = ∑ i ∈ .Ico ⌈u * N⌉₊ N, f i := by
  rw [tsum_eq_sum (s := .Ico ⌈u * N⌉₊ N)]
  · apply Finset.sum_congr rfl
    simp +contextual [Nat.ceil_le, le_div_iff₀, div_lt_iff₀, hN]
  · simp +contextual [Nat.ceil_le, le_div_iff₀, div_lt_iff₀, hN]

include bound hG hG' hpos in
private lemma eventually_lt_sum_range_div {c : ℝ} (hc : c < A) :
    ∀ᶠ N : ℕ in atTop, c < (∑ i ∈ .range N, f i) / N := by
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c < _ := (by fun_prop : ContinuousWithinAt
      (fun ε ↦ A * (1 - 3 * ε)) (Ioi 0) 0) (Ioi_mem_nhds (by grind))
  obtain ⟨ε, _, hε, _⟩ := (hg.and (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/3))).exists
  obtain ⟨ψ, h1, h2, h3, -, h5, _, -⟩ := exists_cutoff hε (by linarith : ε < 2 * ε)
    (by linarith) (by linarith : 1 - ε < 1)
  filter_upwards [(tendsto_sum_div_smooth_real bound hG hG' hpos h1 h2 h3).comp
    tendsto_natCast_atTop_atTop (Ioi_mem_nhds (by nlinarith [A_nonneg bound hG hG' hpos])
    (a := c)), eventually_gt_atTop 0] with N hN1 _
  have : (0 : ℝ) < N := by norm_cast
  refine hN1.trans_le ?_
  simp only [comp_apply]
  grw [(h5.trans (indicator_le_indicator_of_subset (by grind : Ioo ε 1 ⊆ Ico 0 1) (by simp))) _,
    tsum_mul_indicator_Ico this, zero_mul, Nat.ceil_zero, Nat.Ico_zero_eq_range]
  exacts [hpos _, summable_mul h2 this, summable_mul (hasCompactSupport_indicator_Ico 0 1) this]

include bound hG hG' hpos in
private lemma eventually_sum_range_div_lt {c : ℝ} (hc : A < c) :
    ∀ᶠ N : ℕ in atTop, (∑ i ∈ .range N, f i) / N < c := by
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ < c := (by fun_prop : ContinuousWithinAt
      (fun ε ↦ A + 2 * C * ε + ε) (Ioi 0) 0) (Iio_mem_nhds (by grind))
  obtain ⟨ε, _, hε, _⟩ := (hg.and (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))).exists
  obtain ⟨ψ, h1, h2, h3, h4, -, -, _⟩ := exists_cutoff hε (by linarith : ε < 2 * ε)
    (by linarith) (by linarith : 1 < 1 + ε)
  have hcψ : A * ∫ y in Ioi 0, ψ y < c - 2 * C * ε - ε := by
    nlinarith [A_nonneg bound hG hG' hpos]
  filter_upwards [(tendsto_sum_div_smooth_real bound hG hG' hpos h1 h2 h3).comp
    tendsto_natCast_atTop_atTop (Iio_mem_nhds hcψ), eventually_gt_atTop 0,
    (tendsto_const_div_atTop_nhds_zero_nat C).eventually (gt_mem_nhds hε)] with N hN1 _ hN3
  have hN : (0 : ℝ) < N := by norm_cast
  grw [← Finset.sum_range_add_sum_Ico _ (by rw [Nat.ceil_le]; nlinarith : ⌈2 * ε * N⌉₊ ≤ N),
    add_div, ← tsum_mul_indicator_Ico hN, ((indicator_le_indicator_of_subset Ico_subset_Icc_self
    (by simp)).trans h4) _, (by exact hN1 : (∑' n, f n * ψ (n / N)) / N < _),
    bound, Nat.ceil_lt_add_one, mul_add, add_div, mul_one, hN3]
  · field_simp; grind
  · exact C_nonneg bound hpos
  · positivity
  exacts [hpos _, summable_mul (hasCompactSupport_indicator_Ico _ _) hN, summable_mul h2 hN]

include bound hG hG' hpos in
/-- The *Wiener-Ikehara Tauberian Theorem*, summing over naturals `n < N`; see
`WienerIkehara.tendsto_sum_div` for the version summing over reals `n ≤ x`. -/
theorem tendsto_sum_range_div : Tendsto (fun N ↦ (∑ i ∈ .range N, f i) / N) atTop (𝓝 A) :=
  tendsto_order.mpr ⟨fun _ ↦ eventually_lt_sum_range_div bound hG hG' hpos,
    fun _ ↦ eventually_sum_range_div_lt bound hG hG' hpos⟩

include bound hG hG' hpos in
/-- The *Wiener-Ikehara Tauberian Theorem*, summing over naturals `n ≤ x` for real `x`; see
`WienerIkehara.tendsto_sum_range_div` for the version summing over naturals `n < N`. -/
theorem tendsto_sum_div : Tendsto (fun x ↦ (∑ n ∈ .Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A) := by
  have : Tendsto (fun x ↦ (∑ i ∈ .range (⌊x⌋₊ + 1), f i) / (⌊x⌋₊ + 1) * ((⌊x⌋₊ + 1) / x)) atTop
      (𝓝 A) := by
    rw [← mul_one A]
    apply Tendsto.mul
    · simpa [Function.comp_def] using (tendsto_sum_range_div bound hG hG' hpos).comp
        ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    · convert (tendsto_nat_floor_div_atTop (R := ℝ)).add tendsto_inv_atTop_zero <;> grind
  apply this.congr'
  filter_upwards [eventually_gt_atTop 0] with x
  have : (⌊x⌋₊ : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.range_eq_Icc_zero_sub_one _ (by lia)]
  simp [field]

end WienerIkehara

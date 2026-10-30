/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jose Francisco Antonio Balderas, Vincent Beffara, Alex Kontorovich, Terence Tao,
  Ruben Van de Velde, Arend Mellendijk, Alastair Irving
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.NumberTheory.LSeries.Basic

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The Wiener-Ikehara Tauberian theorem

Let `f : ℕ → ℝ` be non-negative with `∑ n ≤ x, f n ≪ x`, whose `L`-series `F` extends
continuously to `Re s ≥ 1` after subtracting `A / (s - 1)`.  Then
`∑ n < N, f n = A * N + o(N)`.

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
test functions (`lim_integ_G_mul`) and then for all Schwartz functions (`lim_S_one_fourier`).
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
private def Q := (𝓕 ψ).seminorm ℝ 0 0 + (𝓕 ψ).seminorm ℝ 2 0

private lemma Q_nonneg : 0 ≤ ψ.Q := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)

private lemma Q_continuous : Continuous Q :=
  (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp (by fun_prop)).add
    (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2, 0)).comp (by fun_prop))

private lemma norm_fourier_le_Q_mul : ‖𝓕 ψ u‖ ≤ ψ.Q * (1 + u ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)]
  have : ‖𝓕 ψ u‖ ≤ (𝓕 ψ).seminorm ℝ 0 0 := by
    simpa using le_seminorm (𝕜 := ℝ) 0 0 (𝓕 ψ) u
  have : u ^ 2 * ‖𝓕 ψ u‖ ≤ (𝓕 ψ).seminorm ℝ 2 0 := by
    simpa [norm_eq_abs, sq_abs, norm_iteratedFDeriv_zero] using le_seminorm (𝕜 := ℝ) 2 0 (𝓕 ψ) u
  unfold Q
  nlinarith

end SchwartzMap

namespace WienerIkehara

/- The data and hypotheses for the Wiener--Ikehara theorem, supplied as individual hypotheses:
a nonnegative function `f` (`hpos`) obeying a Chebyshev-type bound with constant `C` (`bound`),
an asymptotic constant `A`, and a continuous extension `G` of `s ↦ LSeries f s - A / (s - 1)`
to `re s ≥ 1` (`hG`, `hG'`). -/
variable {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ} (bound : ∀ n, ∑ i ∈ .range n, f i ≤ C * n)
  (hG : ContinuousOn G {s | 1 ≤ s.re})
  (hG' : EqOn G (fun s ↦ LSeries ↗f s - A / (s - 1)) {s | 1 < s.re}) (hpos : 0 ≤ f)

private abbrev c₀ := π⁻¹ * 2⁻¹

include bound hpos in
private lemma C_nonneg : 0 ≤ C := (hpos 0).trans (by simpa using bound 1)

include hpos bound in
private lemma lSeriesSummable {σ : ℝ} (hσ : 1 < σ) : LSeriesSummable ↗f (σ : ℂ) := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ hpos zero_le_one (by simpa)
  have := C_nonneg bound hpos
  refine .of_bound (2 * C) <| (eventually_ge_atTop 1).mono fun n hn ↦ ?_
  rw [norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ hpos k), rpow_one, Real.norm_natCast]
  calc
    _ ≤ ∑ k ∈ .range (n + 1), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg (by grind) fun k _ _ ↦ hpos k
    _ ≤ C * (n + 1) := by simpa using bound (n + 1)
    _ ≤ _ := by nlinarith [(Nat.one_le_cast (α := ℝ)).mpr hn]

section FourierIdentities

private def S₁ (f : ℕ → ℝ) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :=
  ∑' n, term ↗f σ n * φ (c₀ * log (n / x))

private def S₂ (A : ℝ) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :=
  A * ↑(x ^ (1 - σ)) * ∫ u in Ici (- log x), rexp (-u * (σ - 1)) * φ (c₀ * u)

/-- A key statistic in the Wiener--Ikehara analysis involving an exponent `σ`, a test
function `φ`, and a scale parameter `x`. -/
private def S (f : ℕ → ℝ) (A : ℝ) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :=
  S₁ f σ φ x - S₂ A σ φ x

variable {x σ : ℝ} (ψ : 𝓢(ℝ, ℂ))

include bound hpos in
private lemma sum_term_mul_fourier_eq (hx : 0 < x) (hσ : 1 < σ) :
    S₁ f σ (𝓕 ψ) x = ∫ t : ℝ, LSeries ↗f (σ + t * I) * ψ t * x ^ (t * I) :=
  calc
    _ = ∑' n, ∫ t, term ↗f σ n * 𝐞 (-(c₀ * log (n / x) * t)) • ψ t := by
      simp [S₁, fourier_coe, fourier_eq, integral_const_mul]
    _ = ∫ t, ∑' n, _ := by
      refine (integral_tsum (by fun_prop) ?_).symm
      have (n : ℕ) : AEMeasurable fun t ↦
        (‖fourierChar (-(c₀ * log (n / x) * t)) • ψ t‖ₑ : ENNReal) := by fun_prop
      simp_rw [enorm_mul, lintegral_const_mul'' _ (this _), Circle.enorm_smul,
        ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ (ne_top_of_lt ψ.integrable.2)
      simp_rw [enorm_eq_nnnorm, ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal,
          NNReal.summable_coe, (lSeriesSummable bound hpos hσ).norm.toNNReal]
    _ = _ := by
      congr with y
      rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries,
        ← Summable.tsum_smul_const]
      · congr with n
        by_cases hn : n = 0
        · simp [*]
        suffices cexp (-(2 * π * ((↑π)⁻¹ * 2⁻¹ * log (n / x) * y) * I))
            = x ^ (y * I) / n ^ (y * I) by
          simp [Circle.smul_def, fourierChar_apply, cpow_add, field, *]
        simp [cpow_def_of_ne_zero, hx.ne.symm, hn, ← Complex.exp_sub, log_div, ofReal_log, hx.le]
        congr
        field_simp
        grind
      · exact (lSeriesSummable bound hpos hσ).of_re_le_re (by simp)

private lemma integral_exp_mul_fourier_eq (hx : 0 < x) (hσ : 1 < σ) :
    S₂ A σ (𝓕 ψ) x = A * ∫ t, (1 / (σ + t * I - 1)) * ψ t * x ^ (t * I) ∂volume := by
  unfold S₂; rw [mul_assoc]; congr 1
  calc
  _ = ↑(x ^ (1 - σ)) * ∫ u in Ici (-log x),
      ∫ a, (rexp (-u * (σ - 1)) : ℂ) • 𝐞 (-(a * (c₀ * u))) • ψ a := by
    simp_rw [fourier_coe, fourier_real_eq, ← smul_eq_mul, ← integral_smul]
  _ = ↑(x ^ (1 - σ)) * ∫ a, ∫ u in _, _ := by
    congr 1
    suffices Integrable (uncurry fun u a ↦ ((rexp (-u * (σ - 1))) : ℂ) •
      (𝐞 (-(a * (c₀ * u))) : ℂ) • ψ a) _ from integral_integral_swap this
    let f1 := fun (a1 : ℝ) ↦ ‖cexp (-(a1 * (σ - 1)))‖ₑ
    let f2 := (‖ψ ·‖ₑ)
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂_ < ⊤ by
      refine ⟨ by fun_prop, by simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, uncurry] ⟩
    grw [lintegral_prod_mul (by fun_prop) (by fun_prop)]
    suffices IntegrableOn _ (Ici (-log x)) from ENNReal.mul_lt_top this.2 ψ.integrable.2
    norm_cast
    refine .ofReal ?_
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
    exact exp_neg_integrableOn_Ioi _ (by linarith)
  _ = _ := by
    rw [← integral_const_mul]
    congr; ext t
    have : (x : ℂ) ≠ 0 := mod_cast hx.ne.symm
    calc
      _ = ↑(x ^ (1 - σ)) * ((∫ u in Ici (-log x), cexp ((1 - σ - t * I) * u)) * ψ t) := by
        rw [← integral_mul_const]
        congr
        push_cast [Circle.smul_def, fourierChar_apply, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
        field_simp
        grind
      _ = ↑(x ^ (1 - σ)) * (((x:ℂ) ^ (σ - 1 : ℂ) * x ^ (t * I)) * (1 / (σ + t * I - 1)) * ψ t) := by
        rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi (by simp [hσ]), ofReal_neg,
          division_def, neg_mul_comm]
        congr 3
        · rw [ofReal_log hx.le, ← cpow_add _ _ this, cpow_def_of_ne_zero this]
          ring_nf
        · grind
      _ = _ := by
        field_simp
        rw [ofReal_cpow hx.le, ofReal_sub, ← cpow_add _ _ this]
        ring_nf
        simp

include bound hpos hG' in
/-- The main result of this section: an initial Fourier identity expressing a sum of
`f` as an error term of Fourier integral type. -/
private lemma sum_term_mul_sub_mul_integral_eq {ψ : 𝓢(ℝ, ℂ)}
    (hψ : HasCompactSupport ψ) (hx : 1 ≤ x) σ (hσ : 1 < σ) :
    S f A σ (𝓕 ψ) x = ∫ t : ℝ, G (σ + t * I) * ψ t * x ^ (t * I) := by
  have hx' : 0 < x := by linarith
  simp_rw [S, sum_term_mul_fourier_eq bound hpos ψ hx' hσ, integral_exp_mul_fourier_eq ψ hx' hσ]
  have (u : ℝ) : σ + u * I - 1 ≠ 0 := by
    intro h; have := congr(re $h); simp at this; linarith
  have : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (by fun_prop) (by simp [hx'])
  rw [← integral_const_mul, ← integral_sub]
  · refine integral_congr_ae (.of_forall fun u ↦ ?_)
    simp_rw [hG' (by simp [hσ] : 1 < (σ + u * I).re)]
    field_simp
  · have : Continuous fun x : ℝ ↦ LSeries ↗f (σ + x * I) := by
      refine continuous_tsum (fun i ↦ ?_) (lSeriesSummable bound hpos hσ).norm
        (by simp [norm_term_eq])
      by_cases h : i = 0
      · simpa [h] using continuous_const
      · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
          (by simp [h])
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ.mul_left.mul_right
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hψ.mul_left.mul_right.mul_left

end FourierIdentities

section Weight

/-- A weight function appearing in the analysis -/
private def w (t : ℝ) := (t * (1 + (c₀ * log t) ^ 2))⁻¹

variable {a c t x : ℝ} {n : ℕ}

private lemma w_nonneg (ht : 0 ≤ t) : 0 ≤ w t := by unfold w; positivity

private lemma w_deriv (ht : t ≠ 0) : HasDerivAt w
    (- (c₀ ^ 2 * (log t + 1) ^ 2 + (1 - c₀) * (1 + c₀)) * w t ^ 2) t := by
  have : HasDerivAt (fun t ↦ t * (1 + (c₀ * log t) ^ 2))
      (1 + 2 * c₀ ^ 2 * log t + (c₀ * log t) ^ 2) t := by
    convert! (hasDerivAt_id' t).mul ?_ (d' := 2 * c₀ ^ 2 * t⁻¹ * log t) using 1
    · grind
    convert! (((hasDerivAt_log ht).const_mul _).pow (f' := c₀ * t⁻¹) 2).const_add _ using 1
    ring
  convert! this.inv (by positivity) using 1
  simp only [w]; grind

private lemma w_antitone : AntitoneOn w (Ioi 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
    (fun _ _ ↦ (w_deriv (by grind)).continuousAt.continuousWithinAt)
    (fun _ _ ↦ (w_deriv (fun _ ↦ by simp_all)).hasDerivWithinAt)
    (fun x _ ↦ ?_)
  have : 0 < c₀ ^ 2 * (log x + 1) ^ 2 + (1 - c₀) * (1 + c₀) := by
    have : π⁻¹ ≤ 2⁻¹ := by simp [field, two_le_pi]
    positivity [(by nlinarith : 0 < 1 - π⁻¹ * 2⁻¹)]
  simp only [neg_mul, Left.neg_nonpos_iff]
  positivity

private lemma w_integrable (hc : 0 < c) : IntegrableOn (fun t ↦ a * w (t / c)) (Ici 0) := by
  have (t) (ht : 0 < t) : t⁻¹ • (a * c * (1 + (c₀ * (log t - log c)) ^ 2)⁻¹) = a * w (t / c)
      := by
    have : 0 < 1 + (c₀ * (log t - log c)) ^ 2 := by positivity
    simp [w, log_div ht.ne' hc.ne', field]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact ((integrableOn_comp_log_Ioi_zero _).2
    (((integrable_inv_one_add_mul_sq (by positivity)).comp_sub_right _).const_mul _)).congr_fun
    this measurableSet_Ioi

private lemma mul_w_antitoneOn (hx : 0 < x) : AntitoneOn (fun t ↦ x⁻¹ * w (t / x)) (Ioc 0 n) := by
  intro u ⟨_, _⟩ v ⟨_, _⟩ huv
  apply mul_le_mul le_rfl ?_ (w_nonneg (by positivity)) (by positivity)
  exact w_antitone (by rw [mem_Ioi]; positivity) (by rw [mem_Ioi]; positivity) (by grw [huv])

private lemma mul_w_integrableOn (hx : 0 < x) :
    IntegrableOn (fun t ↦ x⁻¹ * w (t / x)) (Icc 0 n) volume :=
  .mono_set (w_integrable (by positivity)) Icc_subset_Ici_self

end Weight

section LimitingFourierIdentity

set_option backward.isDefEq.respectTransparency false in
private lemma limiting_cor_aux {ψ : ℝ → ℂ} :
    Tendsto (fun x : ℝ ↦ ∫ t, ψ t * x ^ (t * I)) atTop (𝓝 0) := by
  have : ∀ᶠ x : ℝ in atTop, ∫ t, ψ t * x ^ (t * I) = ∫ t, ψ t * exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx'
    refine integral_congr_ae (Eventually.of_forall (fun _ ↦ ?_))
    simp [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx', mul_assoc]
  simp_rw [tendsto_congr' this]
  convert_to Tendsto (fun x ↦ 𝓕 ψ (-c₀ * log x)) atTop (𝓝 0)
  · ext; congr with _
    simp only [← ofReal_mul, mul_comm (ψ _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg]
    congr; norm_cast; field_simp
  exact (zero_at_infty_fourier ψ).comp <| Tendsto.mono_right
    (tendsto_log_atTop.const_mul_atTop_of_neg (by simp [pi_pos])) atBot_le_cocompact

private abbrev C₀ := 1 + ∫ t in Ioi 0, w t

private lemma C₀_nonneg : 0 ≤ C₀ :=
  add_nonneg zero_le_one (setIntegral_nonneg measurableSet_Ioi (by grind [w_nonneg]))

variable {x : ℝ} (Ψ : 𝓢(ℝ, ℂ))

include bound hpos in
private lemma bound_sum_log_range (hx : 1 ≤ x) (n : ℕ) :
    ∑ i ∈ .range n, ‖f i‖ / i * (1 + (c₀ * log (i / x)) ^ 2)⁻¹ ≤ C * C₀ := by
  have hxne : x ≠ 0 := by linarith
  have := C_nonneg bound hpos
  calc
    _ ≤ ∑ i ∈ .range n, ‖f i‖ * (if i = 0 then 1 else x⁻¹ * w (i / x)) := by
      gcongr 1 with i
      by_cases i = 0 <;> simp [*, w, field]
    _ ≤ C * ∑ i ∈ .range n, (if i = 0 then 1 else x⁻¹ * w (i / x)):= by
      rw [Finset.mul_sum]
      apply Finset.sum_mul_le_sum_mul_of_sum_range_le
        (fun k _ ↦ by simpa [mul_comm, Real.norm_of_nonneg (hpos _)] using bound k)
      · intro i
        by_cases i = 0 <;> simp only [w, *, ↓reduceIte, Pi.zero_apply] <;> positivity
      · have (i : ℕ) : x⁻¹ * w (i / x) ≤ 1 := by
          unfold w
          by_cases hi : i = 0
          · simp [hi]
          · grw [← sq_nonneg, ← (mod_cast by lia : 1 ≤ (i : ℝ))]; simp [field]
        intro i _ j _ _; by_cases i = 0 <;> by_cases j = 0 <;> simp only [↓reduceIte, le_refl, *]
        · lia
        · gcongr; apply w_antitone _ _ (by gcongr) <;> rw [mem_Ioi] <;> positivity
    _ ≤ _ := by
      gcongr
      by_cases h : n = 0
      · simp [h, C₀_nonneg]
      have : Finset.range n = {0} ∪ .Ico 1 n := by grind
      simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
        false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
      convert_to! ∑ i ∈ .Ico 1 n, x⁻¹ * w (i / x) ≤ _
      · exact Finset.sum_congr rfl (by grind)
      simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
      trans ∫ t in 0..↑(n - 1), x⁻¹ * w (t / x)
      · simpa using @AntitoneOn.sum_le_integral_of_integrableOn 0 (n - 1)
          (fun t ↦ x⁻¹ * w (t / x)) (by simpa using mul_w_antitoneOn (by positivity))
          (by simpa using mul_w_integrableOn (by positivity))
      rw [intervalIntegral.integral_comp_div (x⁻¹ * w ·) hxne]
      simp only [intervalIntegral.integral_const_mul]
      have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
      simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, this, ↓reduceIte, uIoc_of_le,
        smul_eq_mul, one_mul, zero_div, mul_inv_cancel₀ hxne, ← mul_assoc]
      apply integral_mono_measure
      · exact Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
      · exact eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun x hx ↦ w_nonneg hx.le
      · simpa using! (w_integrable (a := 1) zero_lt_one).mono_set Ioi_subset_Ici_self

include bound hpos in
private lemma summable_sum_log_range (hx : 1 ≤ x) :
    Summable fun n ↦ ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ := summable_of_sum_range_le
  (fun _ ↦ by positivity) (fun n ↦ by simpa using bound_sum_log_range bound hpos hx n)

include bound hpos in
private theorem tendsto_S₁ (hx : 1 ≤ x) :
    Tendsto (fun σ ↦ S₁ f σ (𝓕 Ψ) x) (𝓝[>] 1) (𝓝 (S₁ f 1 (𝓕 Ψ) x)) := by
  unfold S₁
  refine tendsto_tsum_of_dominated_convergence
    ((summable_sum_log_range bound hpos hx).mul_left Ψ.Q) (fun n ↦ ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ (hσ : 1 < σ) n
    by_cases h : n = 0
    · simp [h]
    simp only [norm_mul, ofReal_re, h, ↓reduceIte, norm_term_eq]
    grw [Ψ.norm_fourier_le_Q_mul, ← hσ]
    · simp; grind
    · exact_mod_cast (by lia)
    · positivity [Ψ.Q_nonneg]

private theorem tendsto_S₂ (hx : 1 ≤ x) :
    Tendsto (fun σ ↦ S₂ A σ (𝓕 Ψ) x) (𝓝[>] 1) (𝓝 (S₂ A 1 (𝓕 Ψ) x)) := by
  apply Tendsto.mul
  · suffices Tendsto (fun σ : ℝ ↦ x ^ (1 - σ)) (𝓝[>] 1) (𝓝 1) by
      simpa using ((continuous_ofReal.tendsto 1).comp this).const_mul ↑A
    have : Tendsto (fun σ : ℝ ↦ σ) (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ : ℝ ↦ 1 - σ) (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (by grind)
  have : Integrable (fun t ↦ max |x| 1 * (Ψ.Q / (1 + (c₀ * t) ^ 2)))
      (volume.restrict (Ici (-log x))) := by
    simp_rw [div_eq_mul_inv]
    exact (((integrable_inv_one_add_sq.comp_mul_left'
      (by positivity)).const_mul _).const_mul _).restrict
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ this ?_
  · have := (𝓕 Ψ).continuous
    exact Eventually.of_forall (fun _ ↦ Continuous.aestronglyMeasurable (by fun_prop))
  · apply eventually_of_mem (U := Ioo 1 2)
    · apply Ioo_mem_nhdsGT_of_mem; simp
    · intro σ ⟨_, _⟩
      rw [ae_restrict_iff' measurableSet_Ici]
      apply Eventually.of_forall
      intro t (ht : - log x ≤ t)
      rw [norm_mul]
      refine mul_le_mul ?_ (Ψ.norm_fourier_le_Q_mul _) (norm_nonneg _) (by grind [abs_nonneg])
      norm_cast
      have := log_nonneg hx
      grw [norm_eq_abs, abs_exp, ← ht, neg_neg, (by linarith : σ - 1 ≤ 1)]
      grind [Real.exp_log, abs_of_nonneg]
  · refine Eventually.of_forall fun x ↦ ?_
    suffices Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝 1) (𝓝 1) by
      simpa using Tendsto.mono_left (this.mul_const _) nhdsWithin_le_nhds
    suffices Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using this.tendsto 1
    fun_prop

include bound hpos in
private theorem lim_S_fourier (hx : 1 ≤ x) : Tendsto (fun σ ↦ S f A σ (𝓕 Ψ) x) (𝓝[>] 1)
      (𝓝 (S f A 1 (𝓕 Ψ) x)) := by
  unfold S
  exact (tendsto_S₁ bound hpos Ψ hx).sub (tendsto_S₂ Ψ hx)

include hG in
private theorem lim_integ_G_mul {Ψ : 𝓢(ℝ, ℂ)} (hΨ : HasCompactSupport Ψ) (hx : 1 ≤ x) :
    Tendsto (fun σ : ℝ ↦ ∫ t : ℝ, G (σ + t * I) * Ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * Ψ t * x ^ (t * I))) := by
  by_cases h : tsupport Ψ = ∅
  · simp [tsupport_eq_empty_iff.mp h]
  obtain ⟨a₀, ha₀⟩ := nonempty_iff_ne_empty.mpr h
  have l1 : IsCompact (reProdIm (Icc 1 2) (tsupport Ψ)) := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport Ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm hΨ.isBounded
  have hsub : reProdIm (Icc 1 2) (tsupport Ψ) ⊆ {s : ℂ | 1 ≤ s.re} :=
    fun z hz ↦ (mem_reProdIm.mp hz).1.1
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn ⟨1 + a₀ * I, by simp [mem_reProdIm, ha₀]⟩
    (hG.mono hsub).norm
  apply tendsto_integral_filter_of_dominated_convergence (bound := (‖G z‖ * ‖Ψ ·‖))
  · refine eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
      fun u hu ↦ (Continuous.mul ?_ ?_).aestronglyMeasurable
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul Ψ.continuous
    · apply Continuous.const_cpow (by fun_prop); simp; linarith
  · refine eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
      fun u hu ↦ Eventually.of_forall fun v ↦ ?_
    by_cases h : v ∈ tsupport Ψ
    · grw [norm_mul, norm_mul, isMaxOn_iff.mp hmax _ (by simp [mem_reProdIm, hu.1, hu.2, h])]
      have : (x : ℂ) ≠ 0 := mod_cast by linarith
      have : arg x = 0 := by simp [arg_eq_zero_iff]; linarith
      simp [norm_cpow_of_ne_zero, *]
    · have : v ∉ support Ψ := by grind [subset_tsupport]
      simp_all
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hΨ.norm.mul_left
  · apply Eventually.of_forall; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG _ (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) ↦ by simp [hx.le])

include bound hG hG' hpos in
private lemma lim_S_one_fourier {Ψ : 𝓢(ℝ, ℂ)} (hΨ : HasCompactSupport Ψ) :
    Tendsto (S f A 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  apply (limiting_cor_aux (ψ := fun t ↦ G (1 + t * I) * (Ψ t))).congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  unfold S
  apply (tendsto_nhds_unique_of_eventuallyEq (lim_S_fourier bound hpos Ψ hx)
    (lim_integ_G_mul hG hΨ hx) _).symm
  simpa [eventuallyEq_nhdsWithin_iff] using!
    Eventually.of_forall (sum_term_mul_sub_mul_integral_eq bound hG' hpos hΨ hx)

end LimitingFourierIdentity

section LimitingFourierIdentitySchwartz

variable (Ψ : 𝓢(ℝ, ℂ))

private lemma norm_term_mul_le (x : ℝ) (f : ℕ → ℂ) (n : ℕ) :
    ‖(term f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ ≤
      Ψ.Q * (‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (Ψ.norm_fourier_le_Q_mul (1 / (2 * π) * log (n / x)))
    (norm_nonneg (f n / n)) using 1
  · simp [term_of_ne_zero']
  · simp; grind

private lemma integ_fourier_bound (x : ℝ) :
    ‖∫ u in Ici (-log x), 𝓕 Ψ (c₀ * u)‖ ≤ Ψ.Q * (2 * π ^ 2) := by
  have key a : ‖𝓕 Ψ (c₀ * a)‖ ≤ Ψ.Q * (1 + (c₀ * a) ^ 2)⁻¹ := Ψ.norm_fourier_le_Q_mul _
  have := Ψ.Q_nonneg
  have : Integrable fun a ↦ (1 + (c₀ * a) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity)
  grw [norm_integral_le_integral_norm, setIntegral_mono ((this.const_mul Ψ.Q).mono' (by fun_prop)
    (by simp [key])).integrableOn (this.const_mul _).integrableOn key, integral_const_mul,
    setIntegral_le_integral this, Measure.integral_comp_mul_left fun x ↦ (1 + x ^ 2)⁻¹]
  · simp [abs_eq_self.mpr (by simp [pi_nonneg] : 0 ≤ 2 * π)]; grind
  · exact Eventually.of_forall fun _ ↦ by positivity

include bound hpos in
private lemma summable_term_mul {x : ℝ} (hx : 1 ≤ x) :
    Summable fun n ↦ ‖(term ↗f 1 n) * 𝓕 Ψ (c₀ * log (n / x))‖ :=
  .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_term_mul_le Ψ x ↗f)
    (by simpa using (summable_sum_log_range bound hpos hx).const_smul Ψ.Q)

include bound hpos in
/-- The map `φ ↦ S f A 1 (𝓕 φ) x` is linear in the test function. -/
private lemma S_one_sub {x : ℝ} (hx : 1 ≤ x) (φ φ' : 𝓢(ℝ, ℂ)) :
    S f A 1 (𝓕 (φ - φ')) x = S f A 1 (𝓕 φ) x - S f A 1 (𝓕 φ') x := by
  have hFsub (t : ℝ) : 𝓕 (φ - φ') t = 𝓕 φ t - 𝓕 φ' t := by
    simp_rw [← fourierTransformCLM_apply ℂ, map_sub, sub_apply]
  have h₁ : S₁ f 1 (𝓕 (φ - φ')) x = S₁ f 1 (𝓕 φ) x - S₁ f 1 (𝓕 φ') x := by
    unfold S₁; rw [ofReal_one, ← Summable.tsum_sub]
    · exact tsum_congr fun _ ↦ by rw [hFsub]; ring
    · simpa [← summable_norm_iff] using summable_term_mul bound hpos φ hx
    · simpa [← summable_norm_iff] using summable_term_mul bound hpos φ' hx
  have h₂ : S₂ A 1 (𝓕 (φ - φ')) x = S₂ A 1 (𝓕 φ) x - S₂ A 1 (𝓕 φ') x := by
    simp only [S₂, sub_self, rpow_zero, ofReal_one, mul_one, mul_zero, Real.exp_zero,
      one_mul]
    rw [← mul_sub, ← integral_sub]
    · congr 1
      exact setIntegral_congr_fun measurableSet_Ici fun _ _ ↦ hFsub _
    · exact ((𝓕 φ).integrable.comp_mul_left' (by positivity)).restrict
    · exact ((𝓕 φ').integrable.comp_mul_left' (by positivity)).restrict
  unfold S; rw [h₁, h₂]; ring

include bound hpos in
/-- A uniform bound on `S f A 1 (𝓕 φ) x` in terms of the seminorm `φ.Q`. -/
private lemma norm_S_one_le {x : ℝ} (hx : 1 ≤ x) (φ : 𝓢(ℝ, ℂ)) :
    ‖S f A 1 (𝓕 φ) x‖ ≤ φ.Q * (C * C₀ + |A| * (2 * π ^ 2)) := by
  unfold S S₂
  have hS₁ : ‖S₁ f 1 (𝓕 φ) x‖ ≤ φ.Q * C * C₀ := calc
    _ ≤ φ.Q • ∑' n, ‖f n‖ / n * (1 + (c₀ * log (n / x)) ^ 2)⁻¹ := by
      have hsum : Summable fun n ↦ ‖f n‖ / n * ((1 + (c₀ * (log (n / x))) ^ 2)⁻¹) := by
        simpa using summable_sum_log_range bound hpos hx
      unfold S₁
      grw [ofReal_one, norm_tsum_le_tsum_norm (summable_term_mul bound hpos _ hx),
        (summable_term_mul bound hpos _ hx).tsum_mono (by simpa using hsum.const_smul φ.Q)
        (norm_term_mul_le _ x ↗f), ← Summable.tsum_const_smul _ hsum]
      simp
    _ ≤ _ := by
      grw [smul_eq_mul, mul_assoc, tsum_le_of_sum_range_le (fun _ ↦ by positivity)]
      exacts [φ.Q_nonneg, bound_sum_log_range bound hpos hx]
  grw [norm_sub_le, hS₁, norm_mul]
  simp only [sub_self, rpow_zero, ofReal_one, mul_one, norm_real, norm_eq_abs, mul_zero,
    Real.exp_zero, one_mul]
  have := C_nonneg bound hpos
  have := C₀_nonneg
  grw [integ_fourier_bound φ x]
  exact le_of_eq (by ring)

include bound hG hG' hpos in
private lemma lim_S_one_fourier_schwartz : Tendsto (S f A 1 (𝓕 Ψ)) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨φ, hφQ : _ < ε / 2, hφcs⟩ := SchwartzMap.dense_hasCompactSupport.inter_open_nonempty
    {φ | (Ψ - φ).Q * (C * C₀ + |A| * (2 * π ^ 2)) < ε / 2}
    (isOpen_lt ((SchwartzMap.Q_continuous.comp (by fun_prop)).mul continuous_const)
      continuous_const)
    ⟨Ψ, by simpa [Q, sub_self, FourierTransform.fourier_zero, _root_.map_zero] using half_pos hε⟩
  filter_upwards [eventually_ge_atTop 1, Metric.tendsto_nhds.mp
    (lim_S_one_fourier bound hG hG' hpos hφcs) (ε / 2) (half_pos hε)] with x hx hφ
  rw [dist_zero_right] at hφ ⊢
  calc ‖S f A 1 (𝓕 Ψ) x‖
      = ‖S f A 1 (𝓕 (Ψ - φ)) x + S f A 1 (𝓕 φ) x‖ := by
        rw [S_one_sub bound hpos hx Ψ φ]; ring_nf
    _ ≤ ‖S f A 1 (𝓕 (Ψ - φ)) x‖ + ‖S f A 1 (𝓕 φ) x‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add ((norm_S_one_le bound hpos hx (Ψ - φ)).trans_lt hφQ) hφ
    _ = ε := by ring

end LimitingFourierIdentitySchwartz

section Smooth

variable {ψ : ℝ → ℂ}

private lemma comp_exp_support0 (hplus : closure (support ψ) ⊆ Ioi 0) : ∀ᶠ x in 𝓝 0, ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ lt_irrefl 0 <| mem_Ioi.mp (hplus h))

private theorem comp_exp_support (hsupp : HasCompactSupport ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) : HasCompactSupport (ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp ⊢
  exact ⟨tendsto_exp_atBot <| comp_exp_support0 hplus, tendsto_exp_atTop hsupp.2⟩

/-- If `ψ` vanishes near `0`, then eventually `∫ y in Ioi x⁻¹, ψ y = ∫ y in Ioi 0, ψ y`. -/
private lemma eventually_setIntegral_Ioi_inv_eq (hψ : ∀ᶠ x in 𝓝 0, ψ x = 0) :
    ∀ᶠ x : ℝ in atTop, ∫ y in Ioi x⁻¹, ψ y = ∫ y in Ioi 0, ψ y := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hψ
  filter_upwards [eventually_gt_atTop ε⁻¹] with x hx
  have hx0 : 0 < x := (inv_pos.mpr hε).trans hx
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (inv_pos.mpr hx0).le) fun y ⟨hy, hy'⟩ ↦ h ?_).symm
  rw [Real.dist_eq, sub_zero, abs_of_pos hy]
  exact (not_lt.mp hy').trans_lt (inv_lt_of_inv_lt₀ hε hx)

include bound hG hG' hpos in
/-- A smoothed *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `f` behaves like `A` asymptotically
with respect to smooth weights. -/
lemma tendsto_sum_div_smooth (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ)
    (hplus : closure (support ψ) ⊆ Ioi 0) : Tendsto (fun x ↦ (∑' n, f n * ψ (n / x)) / x)
    atTop (𝓝 (A * ∫ y in Ioi 0, ψ y)) := by
  let h x := rexp (2 * π * x) * ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ fun x ↦ rexp (2 * π * x) := (contDiff_const.mul contDiff_id).exp
    exact (ofRealCLM.contDiff.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ : ∃ g, 𝓕 g = h2.toSchwartzMap h1 := ⟨𝓕⁻ _, fourier_fourierInv_eq _⟩
  have {y} (hy : 0 < y) : y * ψ y = 𝓕 g (c₀ * log y) := by
    simp only [hg, HasCompactSupport.toSchwartzMap_toFun, h]
    field_simp
    rw [Real.exp_log hy]
  have h3 : ∀ᶠ x in atTop,
      S f A 1 (𝓕 g) x = ∑' n, f n * ψ (n / x) / x - A * ∫ y in Ioi 0, ψ y := by
    filter_upwards [eventually_gt_atTop 0,
      eventually_setIntegral_Ioi_inv_eq (comp_exp_support0 hplus)] with x hx hint
    rw [← hint]
    unfold S S₁
    congr
    · ext n
      by_cases hn : n = 0
      · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
      rw [← this (by positivity)]
      have : (n : ℂ) ≠ 0 := by simpa using hn
      have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
      simp [term, hn, field]
    · simp [S₂, hg, HasCompactSupport.toSchwartzMap_toFun, h]
      field_simp; norm_cast
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      left
      have hcont := hsmooth.continuous
      have : HasCompactSupport (rexp • (ψ ∘ rexp)) := (comp_exp_support hsupp hplus).smul_left
      simpa [Real.exp_neg, exp_log hx] using integral_deriv_smul_comp_Ioi (by fun_prop)
        tendsto_exp_atTop (fun t _ ↦ (Real.hasDerivAt_exp t).hasDerivWithinAt)
        (by fun_prop) (hcont.integrable_of_hasCompactSupport hsupp).integrableOn
        ((Continuous.integrable_of_hasCompactSupport (by fun_prop) this).integrableOn
        (s := Ici (-log x)))
  simpa [tendsto_sub_nhds_zero_iff, tsum_div_const] using
    (lim_S_one_fourier_schwartz bound hG hG' hpos g).congr' h3

include bound hG hG' hpos in
/-- A version of smoothed Wiener--Ikehara for real-valued cutoffs. -/
lemma tendsto_sum_div_smooth_real {Ψ : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : closure (support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (𝓝 (A * ∫ y in Ioi 0, Ψ y)) := by
  have : Tendsto (fun x ↦ (∑' n, f n * (ofReal ∘ Ψ) (n / x)) / x) atTop
      (𝓝 (A * ∫ y in Ioi 0, (ofReal ∘ Ψ) y)) := tendsto_sum_div_smooth bound hG hG' hpos
      (ofRealCLM.contDiff.comp hsmooth) (hsupp.comp_left rfl) (by rwa [support_comp_eq]; simp)
  have := (continuous_re.tendsto _).comp this
  simp at this; norm_cast at this

end Smooth

/-- A smooth Urysohn lemma for cutoffs supported away from the
origin, additionally controlling the integral of the cutoff from above and below by the lengths of
`Ioo a d` and `Icc b c` respectively. -/
private lemma exists_cutoff {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∃ ψ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ closure (support ψ) ⊆ Ioi 0 ∧
      indicator (Icc b c) 1 ≤ ψ ∧ ψ ≤ indicator (Ioo a d) 1 ∧
      c - b ≤ ∫ y in Ioi 0, ψ y ∧ ∫ y in Ioi 0, ψ y ≤ d - a := by
  obtain ⟨ψ, h1, h2, h3, h4⟩ := exists_contDiff_support_eq_eq_one_iff
    isOpen_Ioo isClosed_Icc (Icc_subset_Ioo hab hcd)
  have h5 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (h3 ▸ Ioo_subset_Icc_self)
  have h6 := indicator_le' (fun x hx ↦ ((h4 x).mp hx).ge) fun x _ ↦ (h2 (mem_range_self x)).1
  have h7 : ψ ≤ indicator (Ioo a d) 1 := fun x ↦ le_indicator_apply
    (fun _ ↦ (h2 (mem_range_self x)).2) (by grind)
  have h8 : closure (support ψ) ⊆ Ioi 0 := by grind [closure_Ioo]
  have h9 : Integrable ψ := h1.continuous.integrable_of_hasCompactSupport h5
  have h10 : ∫ y in Ioi 0, ψ y = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      notMem_support.1 fun h ↦ hx (h8 (subset_closure h))
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
  unfold HasFiniteSupport
  simp only [support_mul]; apply Finite.inter_of_right; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi ↦ by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

include bound hG hG' hpos in
/-- The *Wiener-Ikehara Tauberian Theorem*, summing over naturals `n < N`; see
`WienerIkehara.tendsto_sum_div` for the version summing over reals `n ≤ x`. -/
theorem tendsto_sum_range_div : Tendsto (fun N ↦ (∑ i ∈ .range N, f i) / N) atTop (𝓝 A) := by
  have hI {u v} (huv : u < v) : HasCompactSupport (indicator (Ico u v) (1 : ℝ → ℝ)) := by
    simpa [HasCompactSupport, tsupport, huv.ne] using isCompact_Icc (a := u) (b := v)
  have hsum {N : ℕ} (hN : (0 : ℝ) < N) (u : ℝ) :
      ∑' n, f n * (indicator (Ico u 1) 1 (n / N)) = ∑ i ∈ .Ico ⌈u * N⌉₊ N, f i := by
    rw [tsum_eq_sum (s := .Ico ⌈u * N⌉₊ N)]
    · apply Finset.sum_congr rfl
      simp +contextual [Nat.ceil_le, le_div_iff₀, div_lt_iff₀, hN]
    · simp +contextual [Nat.ceil_le, le_div_iff₀, div_lt_iff₀, hN]
  rw [tendsto_order]
  refine ⟨fun c _ ↦ ?_, fun c _ ↦ ?_⟩
  · have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c < _ := (by fun_prop : ContinuousWithinAt
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
      hsum this, zero_mul, Nat.ceil_zero, Nat.Ico_zero_eq_range]
    exacts [hpos _, summable_mul h2 this, summable_mul (hI zero_lt_one) this]
  · have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ < c := (by fun_prop : ContinuousWithinAt
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
      add_div, ← hsum hN, ((indicator_le_indicator_of_subset Ico_subset_Icc_self
      (by simp)).trans h4) _, (by exact hN1 : (∑' n, f n * ψ (n / N)) / N < _),
      bound, Nat.ceil_lt_add_one, mul_add, add_div, mul_one, hN3]
    · field_simp; grind
    · exact C_nonneg bound hpos
    · positivity
    exacts [hpos _, summable_mul (hI (by linarith)) hN, summable_mul h2 hN]

include bound hG hG' hpos in
/-- The *Wiener-Ikehara Tauberian Theorem*, summing over naturals `n ≤ x` for real `x`; see
`WienerIkehara.tendsto_sum_range_div` for the version summing over naturals `n < N`. -/
theorem tendsto_sum_div : Tendsto (fun x : ℝ ↦ (∑ n ∈ .Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A) := by
  have : Tendsto (fun x : ℝ ↦ (∑ i ∈ .range (⌊x⌋₊ + 1), f i) / (⌊x⌋₊ + 1) * ((⌊x⌋₊ + 1) / x)) atTop
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

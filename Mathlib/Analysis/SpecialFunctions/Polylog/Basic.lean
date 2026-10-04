/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib

/-!
# Polylog

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

public noncomputable section

open Set Filter Topology MeasureTheory

namespace Complex

variable {s z : ℂ} {t : ℝ} {n : ℕ}

theorem notMem_Ici_one_reProdIm_of_norm_lt_one (hz : ‖z‖ < 1) : z ∉ Set.Ici 1 ×ℂ {0} := by
  contrapose! hz
  exact hz.left.trans <| re_le_norm z

theorem compl_Ici_one_reProdIm_mem_nhds_of_notMem
    (hz : z ∉ Set.Ici 1 ×ℂ {0}) : (Ici 1 ×ℂ {0})ᶜ ∈ 𝓝 z :=
  ClosedIciTopology.isClosed_Ici 1 |>.reProdIm (T1Space.t1 0) |>.compl_mem_nhds hz

private abbrev mem_of_notMem := compl_Ici_one_reProdIm_mem_nhds_of_notMem (z := z)

/-- TODO: doc -/
@[expose, pp_nodot] def polylogKernel (z : ℂ) (t : ℝ) : ℂ :=
  z / (cexp t - z)

private lemma exp_sub_ne_zero_of (ht : 0 ≤ t) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    cexp t - z ≠ 0 := by
  intro nh
  simp [← sub_eq_zero.mp nh, mem_reProdIm, exp_ofReal_re, ht.not_gt] at hz

private theorem mul_deriv_polylogKernel (ht : 0 ≤ t) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (fun z => polylogKernel z t) z = - deriv (fun t => polylogKernel z t) t := by
  have : cexp t - z ≠ 0 := exp_sub_ne_zero_of ht hz
  have : deriv ofReal t = 1 := hasDerivAt_id (t : ℂ) |>.comp_ofReal.deriv
  unfold polylogKernel
  simp (disch := first | assumption | fun_prop | simp) [this]
  ring

/-- TODO: doc -/
@[expose, pp_nodot] def polylogIntegral (s z : ℂ) : ℂ :=
  1 / Gamma s * mellin (polylogKernel z) s

private lemma mul_deriv_polylogIntegral_add_one_aux1 (hs : 0 < s.re) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    deriv (fun x ↦ ∫ (t : ℝ) in Ioi 0, ↑t ^ s * polylogKernel x t) z =
      ∫ (t : ℝ) in Ioi 0, deriv (fun z ↦ ↑t ^ s * polylogKernel z t) z := by
  obtain ⟨ε, hε₀, hε⟩ : ∃ ε > 0, Metric.ball z ε ⊆ (Ici 1 ×ℂ {0})ᶜ := by
    sorry
  set F : ℂ -> ℝ -> ℂ := fun z t => t ^ s * polylogKernel z t
  have hF (w : ℂ) (hw : w ∉ Set.Ici 1 ×ℂ {0}) : ContinuousOn (F w) (Ioi 0) := by
    sorry
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (x₀ := z) (s := Metric.ball z ε) (μ := volume.restrict (Ioi 0))
    (F := F) (F' := fun z t => deriv (fun z => t ^ s * polylogKernel z t) z)
    (bound := fun t => sorry)
    (Metric.ball_mem_nhds z hε₀)
    (by filter_upwards [Metric.ball_mem_nhds z hε₀] with w hw using
        ContinuousOn.aestronglyMeasurable (hF w <| hε hw) measurableSet_Ioi)
    (by {
      -- use mellin here
      sorry
    })
    (by {

    })
    (by {

    })
    (by {

    })
    (by {

    })
  apply HasDerivAt.deriv
  tauto

private lemma mul_deriv_polylogIntegral_add_one_aux2 (hs : 0 < s.re) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    -∫ t : ℝ in Ioi 0, t ^ s * deriv (fun t => polylogKernel z t) t =
      ∫ t : ℝ in Ioi 0, polylogKernel z t * deriv (fun t : ℝ => (t : ℂ) ^ s) t := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  set u : ℝ -> ℂ := fun t : ℝ => (t : ℂ) ^ s
  set v : ℝ -> ℂ := polylogKernel z
  have hdu (t : ℝ) (ht : 0 < t) : HasDerivAt u (deriv u t) t :=
    hasDerivAt_ofReal_cpow_const ht.ne' hs₀ |>.differentiableAt.hasDerivAt
  have hdv (t : ℝ) (ht : 0 < t) : HasDerivAt v (deriv v t) t :=
    DifferentiableAt.hasDerivAt <| DifferentiableAt.fun_div
      (by fun_prop) (by fun_prop) (exp_sub_ne_zero_of ht.le hz)
  have huv0 : Tendsto (u * v) (𝓝 0) (𝓝 0) := by
    have : (u * v) 0 = 0 := by simp [u, hs₀]
    refine this ▸ ContinuousAt.tendsto ?_
    have hu : Continuous u := continuous_ofReal_cpow_const hs
    have hv : ContinuousAt v 0 := ContinuousAt.div₀ continuousAt_const (by fun_prop) fun nh => by
      simp [sub_eq_zero] at nh
      simp [← nh, mem_reProdIm] at hz
    fun_prop
  have huvinf : Tendsto (u * v) atTop (𝓝 0) := by
    sorry
  have := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hdu hdv
    (by {

    })
    (by {

    })
    (Tendsto.mono_left huv0 nhdsWithin_le_nhds) huvinf
  grind

theorem mul_deriv_polylogIntegral_add_one (hs : 0 < s.re) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (polylogIntegral (s + 1)) z = polylogIntegral s z := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  have hΓs₀ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  unfold polylogIntegral mellin
  simp only [deriv_const_mul_field', Gamma_add_one s hs₀, field, add_sub_cancel_right, smul_eq_mul]
  calc
    _ = z * (∫ t : ℝ in Ioi 0, deriv (fun z : ℂ => t ^ s * polylogKernel z t) z) :=
      congrArg _ <| mul_deriv_polylogIntegral_add_one_aux1 hs hz
    _ = ∫ t : ℝ in Ioi 0, t ^ s * (z * deriv (fun z : ℂ => polylogKernel z t) z) := by
      simp only [deriv_const_mul_field', ← integral_const_mul]
      ring_nf
    _ = ∫ t : ℝ in Ioi 0, t ^ s * - deriv (fun t : ℝ => polylogKernel z t) t :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        congr_arg _ <| mul_deriv_polylogKernel ht.le hz
    _ = - ∫ t : ℝ in Ioi 0, t ^ s * deriv (fun t : ℝ => polylogKernel z t) t := by
      simp [integral_neg]
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * deriv (fun t : ℝ => (t : ℂ) ^ s) t :=
      mul_deriv_polylogIntegral_add_one_aux2 hs hz
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * (s * t ^ (s - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => congr(polylogKernel z t * $(?_))--$
      exact deriv_ofReal_cpow_const ht.ne' hs₀
    _ = ∫ t : ℝ in Ioi 0, s * t ^ (s - 1) * polylogKernel z t:=
      congr(∫ t : ℝ in Ioi 0, $(by ring))--$
    _ = s * ∫ t : ℝ in Ioi 0, t ^ (s - 1) * polylogKernel z t := by
      rw [← integral_const_mul]
      ring_nf

/-- TODO: doc -/
private def polylogAux1 : ℕ -> ℂ -> ℂ -> ℂ
  | 0 => polylogIntegral
  | n + 1 => fun s z : ℂ => z * deriv (polylogAux1 n (s + 1)) z

/-- TODO: doc -/
private def polylogAux2 (s z : ℂ) : ℂ :=
  polylogAux1 ⌊1 - s.re⌋₊ s z

open Classical in
/-- TODO: doc -/
@[irreducible, pp_nodot] def polylog (s z : ℂ) : ℂ :=
  if z ∉ Set.Ici 1 ×ℂ {0} then polylogAux2 s z else
    limUnder (𝓝[{ z : ℂ | z.im ≤ 0 }] z) (polylogAux2 s)

private theorem polylogAux1_zero : polylogAux1 0 = polylogIntegral := rfl

private theorem polylogAux1_add_one (n : ℕ) :
    polylogAux1 (n + 1) = fun s z : ℂ => z * deriv (polylogAux1 n (s + 1)) z := rfl

private theorem polylogAux2_of_re_pos (hs : 0 < s.re) : polylogAux2 s = polylogIntegral s := by
  unfold polylogAux2
  convert congrFun polylogAux1_zero s
  refine Nat.floor_eq_zero.mpr ?_
  simpa

private theorem polylog_of_notMem (hz : z ∉ Set.Ici 1 ×ℂ {0}) : polylog s z = polylogAux2 s z := by
  simp [polylog, hz]

private theorem deriv_polylog_of_notMem (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    deriv (polylog s) z = deriv (polylogAux2 s) z := by
  apply EventuallyEq.deriv_eq
  filter_upwards [mem_of_notMem hz] with z hz using polylog_of_notMem hz

-- main property theorem
-- TODO: for `s` a non-positive integers i.e. `{..., -3, -2, -1, 0}`,
-- there is no branch cut but only a pole `z = 1` and `Li_s` is a rational function
-- so we prove this under `hs : s ∈ {..., -2, -1}` and `hz : z ≠ 1`,
-- call it `mul_deriv_polylog_add_one'`?
theorem mul_deriv_polylog_add_one (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    z * deriv (polylog (s + 1)) z = polylog s z := by
  rw [polylog_of_notMem hz, deriv_polylog_of_notMem hz]
  unfold polylogAux2
  by_cases hs : 0 < s.re
  · rw [Nat.floor_eq_zero.mpr, Nat.floor_eq_zero.mpr]
    · simp only [polylogAux1_zero, ← mul_deriv_polylogIntegral_add_one hs hz]
    · simpa
    · grind [add_re, one_re]
  · suffices ⌊1 - s.re⌋₊ = ⌊1 - (s + 1).re⌋₊ + 1 by
      rw [this]
      rfl
    rw [← Nat.floor_add_one] <;> simp_all [neg_add_eq_sub]

/-- TODO: doc -/
def polylogSeries (s z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s

theorem _root_.Real.summable_polylogSeries_of_abs_lt {x : ℝ} (y : ℝ) (hx : |x| < 1) :
    Summable fun n : ℕ => x ^ (n + 1) / (n + 1) ^ y := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, -y ≤ k := exists_nat_ge (-y)
  have hg : Summable fun n : ℕ => (n + 1 : ℕ) ^ k * |x| ^ (n + 1) :=
    summable_nat_add_iff (f := fun n : ℕ => n ^ k * |x| ^ n) 1 |>.mpr <|
      summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hx : ‖(|x| : ℝ)‖ < 1)
  refine Summable.of_norm_bounded hg fun n => ?_
  rw [norm_div, norm_pow, ← Nat.cast_add_one, Real.norm_rpow_of_nonneg <| Nat.cast_nonneg _,
    div_eq_mul_inv, mul_comm, ← Real.rpow_neg (mod_cast Nat.zero_le _)]
  grw [Real.rpow_le_rpow_of_exponent_le (mod_cast n.succ_pos) hk, Real.rpow_natCast]
  norm_cast

theorem summable_polylogSeries_of_norm_lt (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => z ^ (n + 1) / (n + 1) ^ s := by
  refine Summable.of_norm ?_
  convert Real.summable_polylogSeries_of_abs_lt (x := ‖z‖) (y := s.re) (by simpa using hz) using 1
  ext n
  rw [norm_div, norm_pow, ← Nat.cast_add_one n, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n) s]
  simp

private lemma mul_deriv_polylogSeries_add_one_aux (hz : ‖z‖ < 1) :
    deriv (fun z : ℂ => ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ (s + 1)) z =
      ∑' n : ℕ, deriv (fun z : ℂ => z ^ (n + 1) / (n + 1) ^ (s + 1)) z := by
  obtain ⟨r, hrz, hr⟩ : ∃ r, r ∈ Ioo ‖z‖ 1 := DenselyOrdered.dense ‖z‖ 1 hz
  have hr₀ : 0 < r := norm_nonneg z |>.trans_lt hrz
  apply HasDerivAt.deriv
  apply hasDerivAt_tsum_of_isPreconnected (y₀ := 0) (t := Metric.ball (0 : ℂ) r)
    (u := fun n : ℕ => (n + 1) * r ^ n / (n + 1) ^ (s.re + 1)) ?_ Metric.isOpen_ball
    Metric.isPreconnected_ball (fun n z' hz' => DifferentiableAt.hasDerivAt (by simp)) ?_
    (by simpa only [Metric.mem_ball, dist_self]) (by simp) (by simpa)
  · conv_lhs =>
      enter [n]
      rw [Real.rpow_add (mod_cast Nat.add_one_pos n), Real.rpow_one, mul_comm]
      rw [mul_div_mul_right (r ^ n) ((↑n + 1) ^ s.re) (mod_cast Nat.add_one_ne_zero n)]
    convert @Real.summable_polylogSeries_of_abs_lt r s.re (by grind) |>.const_smul (1 / r) with n
    simp [field, pow_succ]
  · intro n z' hz'
    simp only [deriv_div_const, differentiableAt_fun_id, deriv_fun_pow, Nat.cast_add,
      Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one, Complex.norm_div,
      Complex.norm_mul, norm_pow]
    norm_cast
    gcongr
    · simp only [Metric.mem_ball, dist_zero_right] at hz'
      exact hz'.le
    · rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos <| mod_cast Nat.add_one_pos n]
      simp

theorem mul_deriv_polylogSeries_add_one (hz : ‖z‖ < 1) :
    z * deriv (polylogSeries (s + 1)) z = polylogSeries s z := calc
  z * deriv (fun z : ℂ => ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ (s + 1)) z
    = z * ∑' n : ℕ, deriv (fun z : ℂ => z ^ (n + 1) / (n + 1) ^ (s + 1)) z :=
    congrArg _ <| mul_deriv_polylogSeries_add_one_aux hz
  _ = ∑' n : ℕ, z * deriv (fun z : ℂ => z ^ (n + 1)) z / (n + 1) ^ (s + 1) := by
    simp only [deriv_div_const, ← tsum_mul_left]
    ring_nf
  _ = ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s := tsum_congr fun n => by
    simp [field, cpow_add (x := n + 1) _ _ (mod_cast by simp), cpow_one]
    ring

private theorem polylogKernel_eq_tsum (ht : 0 < t) (hz : ‖z‖ < 1) :
    polylogKernel z t = ∑' n : ℕ, z ^ (n + 1) * cexp (-t * (n + 1)) := by
  have : ‖z * cexp (-↑t)‖ < 1 := by
    simp only [Complex.norm_mul, norm_exp, neg_re, ofReal_re]
    grw [hz, one_mul]
    grind [Real.exp_le_one_iff]
  conv_rhs =>
    enter [1, n]
    rw [mul_comm (-t : ℂ), ← Nat.cast_add_one, ← nsmul_eq_mul, exp_nsmul, ← mul_pow, pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one this]
  simp [exp_neg, field]
  rfl

private lemma polylogIntegral_eq_polylogSeries_aux (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    ∑' n : ℕ, ∫ t : ℝ in Ioi 0, z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) =
      ∫ t : ℝ in Ioi 0, ∑' n : ℕ, z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) := by
  have hg (c : ℝ) :
      Integrable (fun x => c * (Real.exp (-x) * x ^ (s.re - 1))) (volume.restrict (Ioi 0)) :=
    Real.GammaIntegral_convergent hs |>.const_mul c
  have hb (n : ℕ) : ∀ t ∈ Ioi (0 : ℝ), ‖z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1)))‖ ≤
      ‖z‖ ^ (n + 1) * (Real.exp (-t) * t ^ (s.re - 1)) := fun t (ht : 0 < t) => by
    simp only [neg_mul, mul_left_comm, Complex.norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re,
      one_re, norm_pow, norm_exp, neg_re, mul_re, ofReal_re, add_re, natCast_re, ofReal_im, add_im,
      natCast_im, one_im, add_zero, mul_zero, sub_zero, mul_comm (Real.exp _)]
    gcongr
    nlinarith
  have hi (n : ℕ) : IntegrableOn
      (fun t : ℝ => z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1)))) (Ioi 0) := by
    apply (hg (‖z‖ ^ (n + 1))).mono' (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi) ?_
    · apply ContinuousOn.const_mul (b := _) <| continuousOn_of_forall_continuousAt fun t ht =>
        (continuousAt_ofReal_cpow_const t (s - 1) <| Or.inr ht.ne').mul ?_
      fun_prop
    · exact ae_restrict_iff' measurableSet_Ioi |>.mpr <| .of_forall (hb n)
  refine integral_tsum_of_summable_integral_norm hi ?_
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_) <|
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right (‖z‖ * Real.Gamma s.re)
  apply (setIntegral_mono_on (hi n).norm (hg _) measurableSet_Ioi (hb n)).trans_eq
  rw [integral_const_mul, ← Real.Gamma_eq_integral hs]
  ring

-- main auxiliary theorem
/-- TODO: doc -/
theorem polylogIntegral_eq_polylogSeries (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    polylogIntegral s z = polylogSeries s z := calc
  1 / Gamma s * ∫ t : ℝ in Ioi 0, t ^ (s - 1) * polylogKernel z t
    = 1 / Gamma s * ∫ t : ℝ in Ioi 0, ∑' n : ℕ,
      t ^ (s - 1) * (z ^ (n + 1) * cexp (-t * (n + 1))) := by
    refine congr(1 / Gamma s * $(setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_))--$
    rw [tsum_mul_left, polylogKernel_eq_tsum ht hz]
  _ = 1 / Gamma s * ∫ t : ℝ in Ioi 0, ∑' n : ℕ,
      z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) := by ac_rfl
  _ = 1 / Gamma s * ∑' n : ℕ, ∫ t : ℝ in Ioi 0,
      z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) :=
    congrArg _ <| polylogIntegral_eq_polylogSeries_aux hs hz |>.symm
  _ = ∑' n : ℕ, z ^ (n + 1) * 1 / Gamma s * ∫ t : ℝ in Ioi 0,
      t ^ (s - 1) * cexp (-t * (n + 1)) := by
    simp_rw [← tsum_mul_left, ← integral_const_mul]
    ring_nf
  _ = ∑' n : ℕ, z ^ (n + 1) * 1 / Gamma s * (Gamma s / (n + 1) ^ s) := tsum_congr fun n => by
    congr 1
    have hn : (0 : ℝ) < n + 1 := mod_cast Nat.zero_lt_succ n
    simpa [field, arg_eq_pi_iff, hn.not_gt, mul_comm, inv_cpow_eq_ite] using
      integral_cpow_mul_exp_neg_mul_Ioi hs hn
  _ = ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s := by
    field_simp [Gamma_ne_zero_of_re_pos hs]

private theorem polylog_eq_tsum_add_one_aux (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    polylog s z = polylogSeries s z := by
  rw [polylog_of_notMem <| notMem_Ici_one_reProdIm_of_norm_lt_one hz,
    polylogAux2_of_re_pos hs, polylogIntegral_eq_polylogSeries hs hz]

-- main theorem
/-- TODO: doc -/
theorem polylog_eq_polylogIntegral (hs : 0 < s.re) (hz : z ∉ Set.Ici 1 ×ℂ {0}) :
    polylog s z = polylogIntegral s z := by
  rw [polylog_of_notMem hz, polylogAux2_of_re_pos hs]

-- main theorem
/-- TODO: doc -/
theorem polylog_eq_tsum_add_one (hz : ‖z‖ < 1) :
    polylog s z = polylogSeries s z := by
  revert z
  suffices ∀ z, ‖z‖ < 1 -> polylog (s + ⌊1 - s.re⌋₊) z = polylogSeries (s + ⌊1 - s.re⌋₊) z by
    generalize ⌊1 - s.re⌋₊ = n at *
    induction n with
    | zero => simpa
    | succ n ih =>
      refine fun _ _ => ih (fun z hz => ?_) ‹_›
      rw [← mul_deriv_polylogSeries_add_one hz,
        ← mul_deriv_polylog_add_one <| notMem_Ici_one_reProdIm_of_norm_lt_one hz]
      refine congr(z * $(EventuallyEq.deriv_eq ?_))
      filter_upwards [IsOpen.mem_nhds (Metric.isOpen_ball (x := 0)) (by simpa)] with z hz
      simpa [add_assoc] using this z (by simpa using hz)
  refine fun z hz => polylog_eq_tsum_add_one_aux ?_ hz
  simp only [add_re, natCast_re]
  rcases le_total 0 (1 - s.re) with (_ | _) <;> grind [Nat.lt_floor_add_one (1 - s.re)]

/-- TODO: doc -/
theorem polylog_eq_tsum_pnat (hz : ‖z‖ < 1) :
    polylog s z = ∑' n : ℕ+, z ^ n.val / n ^ s := by
  simp [polylog_eq_tsum_add_one hz, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => z ^ n / n ^ s)]
  rfl

theorem hasSum_polylog (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / (n + 1) ^ s) (polylog s z) :=
  Summable.hasSum_iff (summable_polylogSeries_of_norm_lt hz) |>.mpr <|
    polylog_eq_tsum_add_one hz |>.symm

end Complex

#lint

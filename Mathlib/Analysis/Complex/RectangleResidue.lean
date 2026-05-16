/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Residue theorem for rectangular contours

This file proves the residue theorem for rectangular contours. Mathlib already has
Cauchy–Goursat for rectangles
(`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`)
and the Cauchy integral formula for circles. This file fills the gap between them by
proving the residue formula for rectangular boundary integrals, together with a
rotated principal log branch needed to evaluate the left-edge integral that crosses
the standard cut.

The development proceeds in five stages:

* a notation `Complex.boundaryIntegral` for the oriented boundary integral over
  `[z, w]`, with a Cauchy–Goursat wrapper and additivity/scaling lemmas;
* a rotated principal logarithm `Complex.log_neg z := log (-z) + I·π` with cut on the
  *positive* real axis, plus its derivative and corner-comparison identities with the
  standard `Complex.log`;
* explicit FTC-based evaluations of the four edge integrals of `(s − ρ)⁻¹`;
* a closed-form residue boundary integral
  `∮_{∂[z,w]} (s − ρ)⁻¹ ds = 2πi` for `ρ` strictly inside the rectangle;
* a parametric residue theorem for sums of simple poles plus a holomorphic
  remainder, packaged as `Complex.RectangleResidueData`.

## Main results

* `Complex.hasDerivAt_log_neg`: `Complex.log_neg` has derivative `z⁻¹` on the
  rotated slit plane `{z | -z ∈ slitPlane}`.
* `Complex.boundaryIntegral_inv_sub_eq_two_pi_I`: for `ρ` strictly inside the
  rectangle `[z, w]`, the boundary integral of `(s − ρ)⁻¹` equals `2πi`.
* `Complex.boundaryIntegral_eq_residue_sum`: for a `Complex.RectangleResidueData`
  bundle describing simple poles inside the rectangle plus a holomorphic remainder,
  the boundary integral equals `2πi` times the sum of residues.
* `Complex.boundaryIntegral_single_pole`: the one-pole specialization.

## References

* L. Ahlfors, *Complex Analysis* (3rd ed.), §4.5.
* E. Stein, R. Shakarchi, *Complex Analysis*, Ch. 2 §3 Theorem 3.1.
* W. Rudin, *Real and Complex Analysis* (3rd ed.), §10.42.

## Tags

complex analysis, residue theorem, contour integral, Cauchy formula, rectangular contour
-/

public section

open Filter Topology MeasureTheory intervalIntegral Real
open scoped Topology Interval

namespace Complex

variable {z w ρ : ℂ}

/-! ## Boundary integral over a rectangle -/

/-- The oriented boundary integral of `f` over the rectangle `[z, w]`, in the sign
convention of `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`. -/
noncomputable def boundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
  (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
  I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
  I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- Cauchy–Goursat for the boundary-integral notation: a function continuous on the
closed rectangle and differentiable off a countable subset of the open rectangle has
vanishing boundary integral. -/
theorem boundaryIntegral_eq_zero_of_diffOn
    {f : ℂ → ℂ} {z w : ℂ} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hd : ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \ s,
            DifferentiableAt ℂ f x) :
    boundaryIntegral f z w = 0 := by
  unfold boundaryIntegral
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w s hs hc hd

/-! ## Linearity of the boundary integral -/

/-- The boundary integral is additive in the integrand. -/
theorem boundaryIntegral_add (f g : ℂ → ℂ) (z w : ℂ)
    (hfb : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re)
    (hgb : IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re)
    (hft : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re)
    (hgt : IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re)
    (hfr : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im)
    (hgr : IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) volume z.im w.im)
    (hfl : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
    (hgl : IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) volume z.im w.im) :
    boundaryIntegral (fun s => f s + g s) z w =
      boundaryIntegral f z w + boundaryIntegral g z w := by
  unfold boundaryIntegral
  rw [intervalIntegral.integral_add hfb hgb,
      intervalIntegral.integral_add hft hgt,
      intervalIntegral.integral_add hfr hgr,
      intervalIntegral.integral_add hfl hgl]
  rw [smul_add, smul_add]; ring

/-- The boundary integral pulls a complex constant outside. -/
theorem boundaryIntegral_const_mul (k : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    boundaryIntegral (fun s => k * f s) z w = k * boundaryIntegral f z w := by
  unfold boundaryIntegral
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change k * _ - k * _ + I * (k * _) - I * (k * _) =
        k * (_ - _ + I * _ - I * _)
  ring

/-! ## Finite-sum decomposition -/

/-- Pointwise integrability of a finite sum follows from integrability of each
summand. -/
private lemma intervalIntegrable_finset_sum {ι : Type*} (S : Finset ι)
    {a b : ℝ} (g : ι → ℝ → ℂ)
    (hg : ∀ i ∈ S, IntervalIntegrable (g i) volume a b) :
    IntervalIntegrable (fun x : ℝ => ∑ i ∈ S, g i x) volume a b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact intervalIntegrable_const
  | insert i T hiT ih =>
    have hia : IntervalIntegrable (g i) volume a b :=
      hg i (Finset.mem_insert_self i T)
    have hiS : ∀ j ∈ T, IntervalIntegrable (g j) volume a b :=
      fun j hj' => hg j (Finset.mem_insert_of_mem hj')
    have hsum_S : IntervalIntegrable (fun x => ∑ j ∈ T, g j x) volume a b :=
      ih hiS
    have heq : (fun x : ℝ => ∑ j ∈ insert i T, g j x) =
        fun x : ℝ => g i x + ∑ j ∈ T, g j x := by
      funext x; rw [Finset.sum_insert hiT]
    rw [heq]
    exact hia.add hsum_S

/-- The boundary integral distributes over a finite sum of integrands. -/
theorem boundaryIntegral_finset_sum {ι : Type*} (S : Finset ι)
    (f : ι → ℂ → ℂ) (z w : ℂ)
    (hfb : ∀ i ∈ S,
      IntervalIntegrable (fun x : ℝ => f i (x + z.im * I)) volume z.re w.re)
    (hft : ∀ i ∈ S,
      IntervalIntegrable (fun x : ℝ => f i (x + w.im * I)) volume z.re w.re)
    (hfr : ∀ i ∈ S,
      IntervalIntegrable (fun y : ℝ => f i (w.re + y * I)) volume z.im w.im)
    (hfl : ∀ i ∈ S,
      IntervalIntegrable (fun y : ℝ => f i (z.re + y * I)) volume z.im w.im) :
    boundaryIntegral (fun s => ∑ i ∈ S, f i s) z w =
      ∑ i ∈ S, boundaryIntegral (f i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold boundaryIntegral
    simp only [intervalIntegral.integral_zero, smul_zero, sub_zero, add_zero]
  | insert i T hiT ih =>
    have hfb_i := hfb i (Finset.mem_insert_self i T)
    have hft_i := hft i (Finset.mem_insert_self i T)
    have hfr_i := hfr i (Finset.mem_insert_self i T)
    have hfl_i := hfl i (Finset.mem_insert_self i T)
    have hfb_T : ∀ j ∈ T,
        IntervalIntegrable (fun x : ℝ => f j (x + z.im * I)) volume z.re w.re :=
      fun j hj => hfb j (Finset.mem_insert_of_mem hj)
    have hft_T : ∀ j ∈ T,
        IntervalIntegrable (fun x : ℝ => f j (x + w.im * I)) volume z.re w.re :=
      fun j hj => hft j (Finset.mem_insert_of_mem hj)
    have hfr_T : ∀ j ∈ T,
        IntervalIntegrable (fun y : ℝ => f j (w.re + y * I)) volume z.im w.im :=
      fun j hj => hfr j (Finset.mem_insert_of_mem hj)
    have hfl_T : ∀ j ∈ T,
        IntervalIntegrable (fun y : ℝ => f j (z.re + y * I)) volume z.im w.im :=
      fun j hj => hfl j (Finset.mem_insert_of_mem hj)
    have hsum_b : IntervalIntegrable
        (fun x : ℝ => ∑ j ∈ T, f j (x + z.im * I)) volume z.re w.re :=
      intervalIntegrable_finset_sum T (fun j x => f j (x + z.im * I)) hfb_T
    have hsum_t : IntervalIntegrable
        (fun x : ℝ => ∑ j ∈ T, f j (x + w.im * I)) volume z.re w.re :=
      intervalIntegrable_finset_sum T (fun j x => f j (x + w.im * I)) hft_T
    have hsum_r : IntervalIntegrable
        (fun y : ℝ => ∑ j ∈ T, f j (w.re + y * I)) volume z.im w.im :=
      intervalIntegrable_finset_sum T (fun j y => f j (w.re + y * I)) hfr_T
    have hsum_l : IntervalIntegrable
        (fun y : ℝ => ∑ j ∈ T, f j (z.re + y * I)) volume z.im w.im :=
      intervalIntegrable_finset_sum T (fun j y => f j (z.re + y * I)) hfl_T
    have hpw : (fun s => ∑ j ∈ insert i T, f j s) =
        fun s => f i s + ∑ j ∈ T, f j s := by
      funext s; rw [Finset.sum_insert hiT]
    rw [hpw]
    rw [boundaryIntegral_add (f i) (fun s => ∑ j ∈ T, f j s) z w
          hfb_i hsum_b hft_i hsum_t hfr_i hsum_r hfl_i hsum_l]
    rw [Finset.sum_insert hiT, ih hfb_T hft_T hfr_T hfl_T]

/-! ## Rotated principal logarithm `log_neg`

The standard branch `Complex.log` has its branch cut on the negative real axis. To
evaluate boundary integrals on rectangles whose left edge crosses that cut, we
introduce the rotated branch `log_neg z := log (-z) + I·π`, whose cut is on the
*positive* real axis. -/

/-- A principal logarithm with branch cut on the positive real axis. -/
noncomputable def log_neg (z : ℂ) : ℂ := Complex.log (-z) + I * (π : ℝ)

/-- `log_neg` has derivative `z⁻¹` whenever `-z` lies in the standard slit plane. -/
theorem hasDerivAt_log_neg {z : ℂ} (hz : -z ∈ slitPlane) :
    HasDerivAt log_neg z⁻¹ z := by
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hlogneg : HasDerivAt (fun w : ℂ => Complex.log (-w)) ((-z)⁻¹ * -1) z :=
    (Complex.hasDerivAt_log hz).comp z hneg
  have hsimpl : (-z)⁻¹ * (-1 : ℂ) = z⁻¹ := by
    rw [mul_neg_one, neg_inv, neg_neg]
  rw [hsimpl] at hlogneg
  have hadd := hlogneg.add_const (I * (π : ℝ))
  exact hadd

/-- Real-FTC chain rule for `log_neg`: if `f : ℝ → ℂ` has derivative `f'` at `x`
and `-(f x)` lies in the standard slit plane, then `t ↦ log_neg (f t)` has
derivative `f' / f x` at `x`. -/
theorem hasDerivAt_clog_neg_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ}
    (h₁ : HasDerivAt f f' x) (h₂ : -(f x) ∈ slitPlane) :
    HasDerivAt (fun t => log_neg (f t)) (f' / f x) x := by
  simpa [div_eq_inv_mul, mul_comm] using (hasDerivAt_log_neg h₂).comp x h₁

/-- For points with positive imaginary part, `log_neg` agrees with `Complex.log`. -/
theorem log_neg_eq_log_of_im_pos {ζ : ℂ} (him : 0 < ζ.im) :
    log_neg ζ = Complex.log ζ := by
  have h_arg : arg (-ζ) = arg ζ - π :=
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos him
  have hl : Complex.log (-ζ) = Complex.log ζ - I * (π : ℝ) :=
    Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im, h_arg])
  unfold log_neg; rw [hl]; ring

/-- For points with negative imaginary part, `log_neg` differs from `Complex.log`
by `2πi`. -/
theorem log_neg_eq_log_add_two_pi_I_of_im_neg {ζ : ℂ} (him : ζ.im < 0) :
    log_neg ζ = Complex.log ζ + 2 * (π : ℝ) * I := by
  have h_arg : arg (-ζ) = arg ζ + π :=
    Complex.arg_neg_eq_arg_add_pi_of_im_neg him
  have hl : Complex.log (-ζ) = Complex.log ζ + I * (π : ℝ) :=
    Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im, h_arg])
  unfold log_neg; rw [hl]; ring

/-! ## Edge integrals for `(s − ρ)⁻¹` -/

private lemma slitPlane_bottom_edge (hρ_im_lt : z.im < ρ.im) (x : ℝ) :
    ((x : ℂ) + (z.im : ℂ) * I - ρ) ∈ slitPlane := by
  refine Or.inr ?_
  have him : (((x : ℂ) + (z.im : ℂ) * I - ρ)).im = z.im - ρ.im := by
    simp [Complex.sub_im]
  rw [him]; exact sub_ne_zero.mpr (ne_of_lt hρ_im_lt)

private lemma slitPlane_top_edge (hρ_im_lt : ρ.im < w.im) (x : ℝ) :
    ((x : ℂ) + (w.im : ℂ) * I - ρ) ∈ slitPlane := by
  refine Or.inr ?_
  have him : (((x : ℂ) + (w.im : ℂ) * I - ρ)).im = w.im - ρ.im := by
    simp [Complex.sub_im]
  rw [him]; exact sub_ne_zero.mpr (ne_of_gt hρ_im_lt)

private lemma slitPlane_right_edge (hρ_re_lt : ρ.re < w.re) (y : ℝ) :
    ((w.re : ℂ) + (y : ℂ) * I - ρ) ∈ slitPlane := by
  refine Or.inl ?_
  have hre : (((w.re : ℂ) + (y : ℂ) * I - ρ)).re = w.re - ρ.re := by
    simp [Complex.sub_re]
  rw [hre]; linarith

private lemma neg_left_edge_in_slitPlane (hρ_re_lt : z.re < ρ.re) (y : ℝ) :
    -((z.re : ℂ) + (y : ℂ) * I - ρ) ∈ slitPlane := by
  refine Or.inl ?_
  have hre : (-((z.re : ℂ) + (y : ℂ) * I - ρ)).re = ρ.re - z.re := by
    simp [Complex.sub_re]
  rw [hre]; linarith

/-- Closed-form value of a horizontal-edge integral lying in the slit plane,
expressed via the standard logarithm. -/
private theorem horizEdge_integral_eq {z w ρ : ℂ} {c : ℝ}
    (hmem : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * I - ρ) ∈ slitPlane) :
    (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (c : ℂ) * I - ρ)⁻¹) =
      Complex.log ((w.re : ℂ) + (c : ℂ) * I - ρ) -
      Complex.log ((z.re : ℂ) + (c : ℂ) * I - ρ) := by
  have hinner : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => ((t : ℂ) + (c : ℂ) * I - ρ)) 1 x := fun x => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x :=
      Complex.ofRealCLM.hasDerivAt
    simpa using (h1.add_const ((c : ℂ) * I)).sub_const ρ
  have hφ : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) + (c : ℂ) * I - ρ))
        (1 / ((x : ℂ) + (c : ℂ) * I - ρ)) x := fun x =>
    (hinner x).clog_real (hmem x)
  have hpoint : ∀ x : ℝ,
      ((x : ℂ) + (c : ℂ) * I - ρ)⁻¹ =
        1 / ((x : ℂ) + (c : ℂ) * I - ρ) := fun _ => (one_div _).symm
  rw [show (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (c : ℂ) * I - ρ)⁻¹)
        = ∫ x : ℝ in z.re..w.re, 1 / ((x : ℂ) + (c : ℂ) * I - ρ) from
      intervalIntegral.integral_congr (fun x _ => hpoint x)]
  have hcont : ContinuousOn
      (fun x : ℝ => 1 / ((x : ℂ) + (c : ℂ) * I - ρ)) [[z.re, w.re]] :=
    ContinuousOn.div continuousOn_const
      ((Complex.continuous_ofReal.add continuous_const).sub
        continuous_const).continuousOn
      (fun x _ => slitPlane_ne_zero (hmem x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hφ x) hcont.intervalIntegrable]

/-- Bottom-edge integral of `(s − ρ)⁻¹` evaluated via FTC + standard log. -/
theorem bottomEdge_integral_eq (hρ_im_lt : z.im < ρ.im) :
    (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (z.im : ℂ) * I - ρ)⁻¹) =
      Complex.log ((w.re : ℂ) + (z.im : ℂ) * I - ρ) -
      Complex.log ((z.re : ℂ) + (z.im : ℂ) * I - ρ) :=
  horizEdge_integral_eq (slitPlane_bottom_edge hρ_im_lt)

/-- Top-edge integral of `(s − ρ)⁻¹` evaluated via FTC + standard log. -/
theorem topEdge_integral_eq (hρ_im_lt : ρ.im < w.im) :
    (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (w.im : ℂ) * I - ρ)⁻¹) =
      Complex.log ((w.re : ℂ) + (w.im : ℂ) * I - ρ) -
      Complex.log ((z.re : ℂ) + (w.im : ℂ) * I - ρ) :=
  horizEdge_integral_eq (slitPlane_top_edge hρ_im_lt)

/-- Right-edge integral of `(s − ρ)⁻¹` evaluated via FTC + standard log. -/
theorem rightEdge_integral_eq (hρ_re_lt : ρ.re < w.re) :
    (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * I - ρ)⁻¹) =
      -I * (Complex.log ((w.re : ℂ) + (w.im : ℂ) * I - ρ) -
            Complex.log ((w.re : ℂ) + (z.im : ℂ) * I - ρ)) := by
  set φ : ℝ → ℂ := fun y => Complex.log ((w.re : ℂ) + (y : ℂ) * I - ρ)
  have hinner : ∀ y : ℝ,
      HasDerivAt (fun t : ℝ => ((w.re : ℂ) + (t : ℂ) * I - ρ)) I y := fun y => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y :=
      Complex.ofRealCLM.hasDerivAt
    have h3 := (hasDerivAt_const y ((w.re : ℂ))).add (h1.mul_const I)
    simpa using h3.sub_const ρ
  have hφ : ∀ y : ℝ, HasDerivAt φ (I / ((w.re : ℂ) + (y : ℂ) * I - ρ)) y :=
    fun y => (hinner y).clog_real (slitPlane_right_edge hρ_re_lt y)
  have hpoint : ∀ y : ℝ,
      ((w.re : ℂ) + (y : ℂ) * I - ρ)⁻¹ =
        -I * (I / ((w.re : ℂ) + (y : ℂ) * I - ρ)) := by
    intro y
    have hI2 : (-I) * I = (1 : ℂ) := by
      have : I * I = -1 := Complex.I_mul_I
      linear_combination -this
    rw [mul_div_assoc', hI2, one_div]
  rw [show (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * I - ρ)⁻¹)
        = ∫ y : ℝ in z.im..w.im, -I * (I / ((w.re : ℂ) + (y : ℂ) * I - ρ)) from
      intervalIntegral.integral_congr (fun y _ => hpoint y),
      intervalIntegral.integral_const_mul]
  have hcont : ContinuousOn
      (fun y : ℝ => I / ((w.re : ℂ) + (y : ℂ) * I - ρ)) [[z.im, w.im]] :=
    ContinuousOn.div continuousOn_const
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).continuousOn
      (fun y _ => slitPlane_ne_zero (slitPlane_right_edge hρ_re_lt y))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hφ y) hcont.intervalIntegrable]

/-- Left-edge integral of `(s − ρ)⁻¹` evaluated via FTC + the rotated `log_neg`
branch. The left edge crosses the standard cut, so the standard `Complex.log`
antiderivative does not work directly; `log_neg` (cut on the positive real axis)
is the right branch here. -/
theorem leftEdge_integral_eq (hρ_re_lt : z.re < ρ.re) :
    (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * I - ρ)⁻¹) =
      -I * (log_neg ((z.re : ℂ) + (w.im : ℂ) * I - ρ) -
            log_neg ((z.re : ℂ) + (z.im : ℂ) * I - ρ)) := by
  set φ : ℝ → ℂ := fun y => log_neg ((z.re : ℂ) + (y : ℂ) * I - ρ)
  have hinner : ∀ y : ℝ,
      HasDerivAt (fun t : ℝ => ((z.re : ℂ) + (t : ℂ) * I - ρ)) I y := fun y => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y :=
      Complex.ofRealCLM.hasDerivAt
    simpa using ((hasDerivAt_const y ((z.re : ℂ))).add
      (h1.mul_const I)).sub_const ρ
  have hφ : ∀ y : ℝ,
      HasDerivAt φ (I / ((z.re : ℂ) + (y : ℂ) * I - ρ)) y := fun y =>
    hasDerivAt_clog_neg_real (hinner y)
      (neg_left_edge_in_slitPlane hρ_re_lt y)
  have hpoint : ∀ y : ℝ,
      ((z.re : ℂ) + (y : ℂ) * I - ρ)⁻¹ =
        -I * (I / ((z.re : ℂ) + (y : ℂ) * I - ρ)) := fun _ => by
    have hI2 : (-I) * I = (1 : ℂ) := by linear_combination -Complex.I_mul_I
    rw [mul_div_assoc', hI2, one_div]
  have hne : ∀ y : ℝ, ((z.re : ℂ) + (y : ℂ) * I - ρ) ≠ 0 := fun y h0 =>
    slitPlane_ne_zero (neg_left_edge_in_slitPlane hρ_re_lt y)
      (by rw [h0]; simp)
  rw [show (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * I - ρ)⁻¹)
        = ∫ y : ℝ in z.im..w.im,
            -I * (I / ((z.re : ℂ) + (y : ℂ) * I - ρ)) from
      intervalIntegral.integral_congr (fun y _ => hpoint y),
      intervalIntegral.integral_const_mul]
  have hcont : ContinuousOn
      (fun y : ℝ => I / ((z.re : ℂ) + (y : ℂ) * I - ρ)) [[z.im, w.im]] :=
    ContinuousOn.div continuousOn_const
      ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).continuousOn (fun y _ => hne y)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y _ => hφ y) hcont.intervalIntegrable]

/-! ## Closed-form principal-part rectangle integral -/

/-- Algebraic assembly of the four edge integrals into the boundary integral. Given
closed-form values for the four edges plus the corner identity
`(L_b - L_t) + I·L_r - I·L_l = 2πi`, the boundary integral equals `2πi`. -/
private theorem boundaryIntegral_inv_sub_assemble
    {z w ρ : ℂ} {Lb Lt Lr Ll : ℂ}
    (hb : (∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - ρ)⁻¹) = Lb)
    (ht : (∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - ρ)⁻¹) = Lt)
    (hr : (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * I - ρ)⁻¹) = Lr)
    (hl : (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * I - ρ)⁻¹) = Ll)
    (hcorner : (Lb - Lt) + I * Lr - I * Ll = 2 * (π : ℂ) * I) :
    boundaryIntegral (fun s => (s - ρ)⁻¹) z w = 2 * (π : ℂ) * I := by
  unfold boundaryIntegral
  rw [hb, ht, hr, hl]
  show (Lb - Lt) + I • Lr - I • Ll = 2 * (π : ℂ) * I
  simp only [smul_eq_mul]
  exact hcorner

/-- **Cauchy integral formula on a rectangle.** For `ρ` strictly inside the
rectangle `[z, w]`, the boundary integral of `(s − ρ)⁻¹` equals `2πi`.

This is the rectangular analogue of Mathlib's circle-based Cauchy integral formula
for `(s − ρ)⁻¹`. The proof evaluates each of the four edge integrals using the FTC
with the standard logarithm (three edges) and the rotated branch `log_neg` for the
left edge, then verifies that the corner identity reduces to `2πi`. -/
theorem boundaryIntegral_inv_sub_eq_two_pi_I
    (hρ_re : ρ.re ∈ Set.Ioo z.re w.re) (hρ_im : ρ.im ∈ Set.Ioo z.im w.im) :
    boundaryIntegral (fun s => (s - ρ)⁻¹) z w = 2 * (π : ℂ) * I := by
  obtain ⟨hρ_re_z, hρ_re_w⟩ := hρ_re
  obtain ⟨hρ_im_z, hρ_im_w⟩ := hρ_im
  have hb := bottomEdge_integral_eq (z := z) (w := w) (ρ := ρ) hρ_im_z
  have ht := topEdge_integral_eq (z := z) (w := w) (ρ := ρ) hρ_im_w
  have hr := rightEdge_integral_eq (z := z) (w := w) (ρ := ρ) hρ_re_w
  have hl := leftEdge_integral_eq (z := z) (w := w) (ρ := ρ) hρ_re_z
  have hζTL_im : 0 < ((z.re : ℂ) + (w.im : ℂ) * I - ρ).im := by
    show 0 < (((z.re : ℂ) + (w.im : ℂ) * I - ρ)).im
    simp [Complex.sub_im]; linarith
  have hζBL_im : ((z.re : ℂ) + (z.im : ℂ) * I - ρ).im < 0 := by
    show (((z.re : ℂ) + (z.im : ℂ) * I - ρ)).im < 0
    simp [Complex.sub_im]; linarith
  have hLN_TL := log_neg_eq_log_of_im_pos hζTL_im
  have hLN_BL := log_neg_eq_log_add_two_pi_I_of_im_neg hζBL_im
  set LBL : ℂ := Complex.log ((z.re : ℂ) + (z.im : ℂ) * I - ρ)
  set LTL : ℂ := Complex.log ((z.re : ℂ) + (w.im : ℂ) * I - ρ)
  set LBR : ℂ := Complex.log ((w.re : ℂ) + (z.im : ℂ) * I - ρ)
  set LTR : ℂ := Complex.log ((w.re : ℂ) + (w.im : ℂ) * I - ρ)
  refine boundaryIntegral_inv_sub_assemble hb ht hr hl ?_
  rw [hLN_TL, hLN_BL]
  have hII : I * I = (-1 : ℂ) := Complex.I_mul_I
  linear_combination
    (LBR - LBL - LTR + LTL - 2 * I * (Real.pi : ℂ)) * hII

/-! ## Parametric residue theorem -/

/-- Hypothesis bundle for the parametric residue theorem on a rectangle.

The integrand decomposes as `f s = ∑_{ρ ∈ S} c ρ · (s − ρ)⁻¹ + h s`, where `S` is
the finite set of simple poles (assumed inside the open rectangle), `c ρ` is the
residue at each pole, and `h` is holomorphic on the closed rectangle off a
countable set. The bundle records the integrability hypotheses needed to apply
linearity of the boundary integral. -/
structure RectangleResidueData (z w : ℂ) where
  /-- Finite set of distinct simple-pole locations inside the open rectangle. -/
  S : Finset ℂ
  /-- Residue at each pole. -/
  c : ℂ → ℂ
  /-- Holomorphic remainder. -/
  h : ℂ → ℂ
  /-- The principal-part rectangle integral evaluates to `2πi` for each pole. -/
  principalPart_int :
    ∀ ρ ∈ S, boundaryIntegral (fun s => (s - ρ)⁻¹) z w = 2 * (π : ℂ) * I
  /-- `h` is continuous on the closed rectangle. -/
  h_continuousOn : ContinuousOn h ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
  /-- Countable set off which `h` is differentiable on the open rectangle. -/
  h_off : Set ℂ
  /-- The off-set is countable. -/
  h_off_countable : h_off.Countable
  /-- `h` is differentiable on the open rectangle minus the off-set. -/
  h_differentiableAt :
    ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \ h_off,
        DifferentiableAt ℂ h x
  /-- Principal-part bottom-edge integrability. -/
  pp_int_b : ∀ ρ ∈ S, IntervalIntegrable
    (fun x : ℝ => ((x : ℂ) + z.im * I - ρ)⁻¹) volume z.re w.re
  /-- Principal-part top-edge integrability. -/
  pp_int_t : ∀ ρ ∈ S, IntervalIntegrable
    (fun x : ℝ => ((x : ℂ) + w.im * I - ρ)⁻¹) volume z.re w.re
  /-- Principal-part right-edge integrability. -/
  pp_int_r : ∀ ρ ∈ S, IntervalIntegrable
    (fun y : ℝ => (w.re + (y : ℂ) * I - ρ)⁻¹) volume z.im w.im
  /-- Principal-part left-edge integrability. -/
  pp_int_l : ∀ ρ ∈ S, IntervalIntegrable
    (fun y : ℝ => (z.re + (y : ℂ) * I - ρ)⁻¹) volume z.im w.im
  /-- Remainder bottom-edge integrability. -/
  h_int_b : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + z.im * I))
              volume z.re w.re
  /-- Remainder top-edge integrability. -/
  h_int_t : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + w.im * I))
              volume z.re w.re
  /-- Remainder right-edge integrability. -/
  h_int_r : IntervalIntegrable (fun y : ℝ => h (w.re + (y : ℂ) * I))
              volume z.im w.im
  /-- Remainder left-edge integrability. -/
  h_int_l : IntervalIntegrable (fun y : ℝ => h (z.re + (y : ℂ) * I))
              volume z.im w.im

/-- The integrand assembled from a `RectangleResidueData` bundle:
`f s = ∑_{ρ ∈ S} c ρ · (s − ρ)⁻¹ + h s`. -/
noncomputable def RectangleResidueData.toIntegrand
    {z w : ℂ} (D : RectangleResidueData z w) (s : ℂ) : ℂ :=
  (∑ ρ ∈ D.S, D.c ρ * (s - ρ)⁻¹) + D.h s

/-- **Parametric residue theorem for rectangles.**

If the integrand decomposes as `f s = ∑_{ρ ∈ S} c ρ · (s − ρ)⁻¹ + h s` per the
hypotheses bundled in `RectangleResidueData`, then the boundary integral equals
`2πi · ∑_{ρ ∈ S} c ρ`. The proof combines linearity of the boundary integral,
Cauchy–Goursat for the holomorphic remainder, and the principal-part value at
each pole. -/
theorem boundaryIntegral_eq_residue_sum {z w : ℂ}
    (D : RectangleResidueData z w) :
    boundaryIntegral D.toIntegrand z w =
      (2 * (π : ℂ) * I) * ∑ ρ ∈ D.S, D.c ρ := by
  classical
  have hpp_b : ∀ ρ ∈ D.S, IntervalIntegrable
      (fun x : ℝ => D.c ρ * ((x : ℂ) + z.im * I - ρ)⁻¹)
      volume z.re w.re :=
    fun ρ hρ => (D.pp_int_b ρ hρ).const_mul _
  have hpp_t : ∀ ρ ∈ D.S, IntervalIntegrable
      (fun x : ℝ => D.c ρ * ((x : ℂ) + w.im * I - ρ)⁻¹)
      volume z.re w.re :=
    fun ρ hρ => (D.pp_int_t ρ hρ).const_mul _
  have hpp_r : ∀ ρ ∈ D.S, IntervalIntegrable
      (fun y : ℝ => D.c ρ * (w.re + (y : ℂ) * I - ρ)⁻¹)
      volume z.im w.im :=
    fun ρ hρ => (D.pp_int_r ρ hρ).const_mul _
  have hpp_l : ∀ ρ ∈ D.S, IntervalIntegrable
      (fun y : ℝ => D.c ρ * (z.re + (y : ℂ) * I - ρ)⁻¹)
      volume z.im w.im :=
    fun ρ hρ => (D.pp_int_l ρ hρ).const_mul _
  have hsum_b : IntervalIntegrable
      (fun x : ℝ => ∑ ρ ∈ D.S, D.c ρ * ((x : ℂ) + z.im * I - ρ)⁻¹)
      volume z.re w.re :=
    intervalIntegrable_finset_sum D.S
      (fun ρ x => D.c ρ * ((x : ℂ) + z.im * I - ρ)⁻¹) hpp_b
  have hsum_t : IntervalIntegrable
      (fun x : ℝ => ∑ ρ ∈ D.S, D.c ρ * ((x : ℂ) + w.im * I - ρ)⁻¹)
      volume z.re w.re :=
    intervalIntegrable_finset_sum D.S
      (fun ρ x => D.c ρ * ((x : ℂ) + w.im * I - ρ)⁻¹) hpp_t
  have hsum_r : IntervalIntegrable
      (fun y : ℝ => ∑ ρ ∈ D.S, D.c ρ * (w.re + (y : ℂ) * I - ρ)⁻¹)
      volume z.im w.im :=
    intervalIntegrable_finset_sum D.S
      (fun ρ y => D.c ρ * (w.re + (y : ℂ) * I - ρ)⁻¹) hpp_r
  have hsum_l : IntervalIntegrable
      (fun y : ℝ => ∑ ρ ∈ D.S, D.c ρ * (z.re + (y : ℂ) * I - ρ)⁻¹)
      volume z.im w.im :=
    intervalIntegrable_finset_sum D.S
      (fun ρ y => D.c ρ * (z.re + (y : ℂ) * I - ρ)⁻¹) hpp_l
  have hidem : D.toIntegrand =
      fun s => (∑ ρ ∈ D.S, D.c ρ * (s - ρ)⁻¹) + D.h s := rfl
  rw [hidem]
  rw [boundaryIntegral_add (fun s => ∑ ρ ∈ D.S, D.c ρ * (s - ρ)⁻¹) D.h z w
        hsum_b D.h_int_b hsum_t D.h_int_t hsum_r D.h_int_r hsum_l D.h_int_l]
  rw [boundaryIntegral_eq_zero_of_diffOn
        D.h_off_countable D.h_continuousOn D.h_differentiableAt, add_zero]
  rw [boundaryIntegral_finset_sum D.S (fun ρ s => D.c ρ * (s - ρ)⁻¹) z w
        hpp_b hpp_t hpp_r hpp_l]
  have heach : ∀ ρ ∈ D.S,
      boundaryIntegral (fun s => D.c ρ * (s - ρ)⁻¹) z w =
        D.c ρ * (2 * (π : ℂ) * I) := by
    intro ρ hρ
    rw [boundaryIntegral_const_mul (D.c ρ) (fun s => (s - ρ)⁻¹) z w]
    rw [D.principalPart_int ρ hρ]
  rw [Finset.sum_congr rfl heach]
  rw [← Finset.sum_mul, mul_comm]

/-- **Single-pole specialization** of the residue theorem. If `f s = c · (s − ρ)⁻¹
+ h s` with `h` continuous on the closed rectangle and differentiable off a
countable set in the open rectangle, then the boundary integral equals `2πi · c`. -/
theorem boundaryIntegral_single_pole {z w : ℂ} {ρ c : ℂ} {h : ℂ → ℂ}
    (hpp : boundaryIntegral (fun s => (s - ρ)⁻¹) z w = 2 * (π : ℂ) * I)
    (hh_cont : ContinuousOn h ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hh_off : Set ℂ) (hh_off_c : hh_off.Countable)
    (hh_diff : ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
                   Set.Ioo (min z.im w.im) (max z.im w.im) \ hh_off,
                 DifferentiableAt ℂ h x)
    (pp_b : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + z.im * I - ρ)⁻¹) volume z.re w.re)
    (pp_t : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + w.im * I - ρ)⁻¹) volume z.re w.re)
    (pp_r : IntervalIntegrable
      (fun y : ℝ => (w.re + (y : ℂ) * I - ρ)⁻¹) volume z.im w.im)
    (pp_l : IntervalIntegrable
      (fun y : ℝ => (z.re + (y : ℂ) * I - ρ)⁻¹) volume z.im w.im)
    (h_int_b : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + z.im * I))
                  volume z.re w.re)
    (h_int_t : IntervalIntegrable (fun x : ℝ => h ((x : ℂ) + w.im * I))
                  volume z.re w.re)
    (h_int_r : IntervalIntegrable (fun y : ℝ => h (w.re + (y : ℂ) * I))
                  volume z.im w.im)
    (h_int_l : IntervalIntegrable (fun y : ℝ => h (z.re + (y : ℂ) * I))
                  volume z.im w.im) :
    boundaryIntegral (fun s => c * (s - ρ)⁻¹ + h s) z w = (2 * (π : ℂ) * I) * c := by
  classical
  let D : RectangleResidueData z w :=
    { S := {ρ}
      c := fun _ => c
      h := h
      principalPart_int := fun ρ' hρ' => by
        rw [Finset.mem_singleton.mp hρ']
        exact hpp
      h_continuousOn := hh_cont
      h_off := hh_off
      h_off_countable := hh_off_c
      h_differentiableAt := hh_diff
      pp_int_b := fun ρ' hρ' => by rw [Finset.mem_singleton.mp hρ']; exact pp_b
      pp_int_t := fun ρ' hρ' => by rw [Finset.mem_singleton.mp hρ']; exact pp_t
      pp_int_r := fun ρ' hρ' => by rw [Finset.mem_singleton.mp hρ']; exact pp_r
      pp_int_l := fun ρ' hρ' => by rw [Finset.mem_singleton.mp hρ']; exact pp_l
      h_int_b := h_int_b
      h_int_t := h_int_t
      h_int_r := h_int_r
      h_int_l := h_int_l }
  have hkey := boundaryIntegral_eq_residue_sum D
  have hint : D.toIntegrand = fun s => c * (s - ρ)⁻¹ + h s := by
    funext s
    change (∑ ρ' ∈ ({ρ} : Finset ℂ), c * (s - ρ')⁻¹) + h s
        = c * (s - ρ)⁻¹ + h s
    rw [Finset.sum_singleton]
  have hsum_eq : (∑ ρ' ∈ ({ρ} : Finset ℂ), (fun _ : ℂ => c) ρ') = c :=
    Finset.sum_singleton (a := ρ) (f := fun _ : ℂ => c)
  rw [hint] at hkey
  rw [hkey, hsum_eq]

end Complex

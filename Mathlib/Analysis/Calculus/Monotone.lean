/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.monotone
! leanprover-community/mathlib commit 3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Deriv.Slope
import Mathbin.MeasureTheory.Covering.OneDim
import Mathbin.Order.Monotone.Extension

/-!
# Differentiability of monotone functions

We show that a monotone function `f : ℝ → ℝ` is differentiable almost everywhere, in
`monotone.ae_differentiable_at`. (We also give a version for a function monotone on a set, in
`monotone_on.ae_differentiable_within_at`.)

If the function `f` is continuous, this follows directly from general differentiation of measure
theorems. Let `μ` be the Stieltjes measure associated to `f`. Then, almost everywhere,
`μ [x, y] / Leb [x, y]` (resp. `μ [y, x] / Leb [y, x]`) converges to the Radon-Nikodym derivative
of `μ` with respect to Lebesgue when `y` tends to `x` in `(x, +∞)` (resp. `(-∞, x)`), by
`vitali_family.ae_tendsto_rn_deriv`. As `μ [x, y] = f y - f x` and `Leb [x, y] = y - x`, this
gives differentiability right away.

When `f` is only monotone, the same argument works up to small adjustments, as the associated
Stieltjes measure satisfies `μ [x, y] = f (y^+) - f (x^-)` (the right and left limits of `f` at `y`
and `x` respectively). One argues that `f (x^-) = f x` almost everywhere (in fact away from a
countable set), and moreover `f ((y - (y-x)^2)^+) ≤ f y ≤ f (y^+)`. This is enough to deduce the
limit of `(f y - f x) / (y - x)` by a lower and upper approximation argument from the known
behavior of `μ [x, y]`.
-/


open Set Filter Function Metric MeasureTheory MeasureTheory.Measure IsUnifLocDoublingMeasure

open scoped Topology

/-- If `(f y - f x) / (y - x)` converges to a limit as `y` tends to `x`, then the same goes if
`y` is shifted a little bit, i.e., `f (y + (y-x)^2) - f x) / (y - x)` converges to the same limit.
This lemma contains a slightly more general version of this statement (where one considers
convergence along some subfilter, typically `𝓝[<] x` or `𝓝[>] x`) tailored to the application
to almost everywhere differentiability of monotone functions. -/
theorem tendsto_apply_add_mul_sq_div_sub {f : ℝ → ℝ} {x a c d : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝[≠] x)
    (hf : Tendsto (fun y => (f y - d) / (y - x)) l (𝓝 a))
    (h' : Tendsto (fun y => y + c * (y - x) ^ 2) l l) :
    Tendsto (fun y => (f (y + c * (y - x) ^ 2) - d) / (y - x)) l (𝓝 a) :=
  by
  have L : tendsto (fun y => (y + c * (y - x) ^ 2 - x) / (y - x)) l (𝓝 1) :=
    by
    have : tendsto (fun y => 1 + c * (y - x)) l (𝓝 (1 + c * (x - x))) :=
      by
      apply tendsto.mono_left _ (hl.trans nhdsWithin_le_nhds)
      exact ((tendsto_id.sub_const x).const_mul c).const_add 1
    simp only [_root_.sub_self, add_zero, MulZeroClass.mul_zero] at this 
    apply tendsto.congr' (eventually.filter_mono hl _) this
    filter_upwards [self_mem_nhdsWithin] with y hy
    field_simp [sub_ne_zero.2 hy]
    ring
  have Z := (hf.comp h').mul L
  rw [mul_one] at Z 
  apply tendsto.congr' _ Z
  have : ∀ᶠ y in l, y + c * (y - x) ^ 2 ≠ x := by apply tendsto.mono_right h' hl self_mem_nhdsWithin
  filter_upwards [this] with y hy
  field_simp [sub_ne_zero.2 hy]
#align tendsto_apply_add_mul_sq_div_sub tendsto_apply_add_mul_sq_div_sub

/-- A Stieltjes function is almost everywhere differentiable, with derivative equal to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Lebesgue. -/
theorem StieltjesFunction.ae_hasDerivAt (f : StieltjesFunction) :
    ∀ᵐ x, HasDerivAt f (rnDeriv f.Measure volume x).toReal x :=
  by
  /- Denote by `μ` the Stieltjes measure associated to `f`.
    The general theorem `vitali_family.ae_tendsto_rn_deriv` ensures that `μ [x, y] / (y - x)` tends
    to the Radon-Nikodym derivative as `y` tends to `x` from the right. As `μ [x, y] = f y - f (x^-)`
    and `f (x^-) = f x` almost everywhere, this gives differentiability on the right.
    On the left, `μ [y, x] / (x - y)` again tends to the Radon-Nikodym derivative.
    As `μ [y, x] = f x - f (y^-)`, this is not exactly the right result, so one uses a sandwiching
    argument to deduce the convergence for `(f x - f y) / (x - y)`. -/
  filter_upwards [VitaliFamily.ae_tendsto_rnDeriv (VitaliFamily (volume : Measure ℝ) 1) f.measure,
    rn_deriv_lt_top f.measure volume, f.countable_left_lim_ne.ae_not_mem volume] with x hx h'x h''x
  -- Limit on the right, following from differentiation of measures
  have L1 :
    tendsto (fun y => (f y - f x) / (y - x)) (𝓝[>] x) (𝓝 (rn_deriv f.measure volume x).toReal) :=
    by
    apply
      tendsto.congr' _
        ((ENNReal.tendsto_toReal h'x.ne).comp (hx.comp (Real.tendsto_Icc_vitaliFamily_right x)))
    filter_upwards [self_mem_nhdsWithin]
    rintro y (hxy : x < y)
    simp only [comp_app, StieltjesFunction.measure_Icc, Real.volume_Icc, Classical.not_not.1 h''x]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal]
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le
  -- Limit on the left, following from differentiation of measures. Its form is not exactly the one
  -- we need, due to the appearance of a left limit.
  have L2 :
    tendsto (fun y => (left_lim f y - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rn_deriv f.measure volume x).toReal) :=
    by
    apply
      tendsto.congr' _
        ((ENNReal.tendsto_toReal h'x.ne).comp (hx.comp (Real.tendsto_Icc_vitaliFamily_left x)))
    filter_upwards [self_mem_nhdsWithin]
    rintro y (hxy : y < x)
    simp only [comp_app, StieltjesFunction.measure_Icc, Real.volume_Icc]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal, ← neg_neg (y - x),
      div_neg, neg_div', neg_sub, neg_sub]
    exact div_nonneg (sub_nonneg.2 (f.mono.left_lim_le hxy.le)) (sub_pos.2 hxy).le
  -- Shifting a little bit the limit on the left, by `(y - x)^2`.
  have L3 :
    tendsto (fun y => (left_lim f (y + 1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rn_deriv f.measure volume x).toReal) :=
    by
    apply tendsto_apply_add_mul_sq_div_sub (nhds_left'_le_nhds_ne x) L2
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · apply tendsto.mono_left _ nhdsWithin_le_nhds
      have : tendsto (fun y : ℝ => y + 1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + 1 * (x - x) ^ 2)) :=
        tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul 1)
      simpa using this
    · have : Ioo (x - 1) x ∈ 𝓝[<] x := by apply Ioo_mem_nhdsWithin_Iio;
        exact ⟨by linarith, le_refl _⟩
      filter_upwards [this]
      rintro y ⟨hy : x - 1 < y, h'y : y < x⟩
      rw [mem_Iio]
      nlinarith
  -- Deduce the correct limit on the left, by sandwiching.
  have L4 :
    tendsto (fun y => (f y - f x) / (y - x)) (𝓝[<] x) (𝓝 (rn_deriv f.measure volume x).toReal) :=
    by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      refine' div_le_div_of_nonpos_of_le (by linarith) ((sub_le_sub_iff_right _).2 _)
      apply f.mono.le_left_lim
      have : 0 < (x - y) ^ 2 := sq_pos_of_pos (sub_pos.2 hy)
      linarith
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      refine' div_le_div_of_nonpos_of_le (by linarith) _
      simpa only [sub_le_sub_iff_right] using f.mono.left_lim_le (le_refl y)
  -- prove the result by splitting into left and right limits.
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, ← nhds_left'_sup_nhds_right', tendsto_sup]
  exact ⟨L4, L1⟩
#align stieltjes_function.ae_has_deriv_at StieltjesFunction.ae_hasDerivAt

/-- A monotone function is almost everywhere differentiable, with derivative equal to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Lebesgue. -/
theorem Monotone.ae_hasDerivAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, HasDerivAt f (rnDeriv hf.StieltjesFunction.Measure volume x).toReal x :=
  by
  /- We already know that the Stieltjes function associated to `f` (i.e., `g : x ↦ f (x^+)`) is
    differentiable almost everywhere. We reduce to this statement by sandwiching values of `f` with
    values of `g`, by shifting with `(y - x)^2` (which has no influence on the relevant
    scale `y - x`.)-/
  filter_upwards [hf.stieltjes_function.ae_has_deriv_at,
    hf.countable_not_continuous_at.ae_not_mem volume] with x hx h'x
  have A : hf.stieltjes_function x = f x :=
    by
    rw [Classical.not_not, hf.continuous_at_iff_left_lim_eq_right_lim] at h'x 
    apply le_antisymm _ (hf.le_right_lim (le_refl _))
    rw [← h'x]
    exact hf.left_lim_le (le_refl _)
  rw [hasDerivAt_iff_tendsto_slope, (nhds_left'_sup_nhds_right' x).symm, tendsto_sup,
    slope_fun_def_field, A] at hx 
  -- prove differentiability on the right, by sandwiching with values of `g`
  have L1 :
    tendsto (fun y => (f y - f x) / (y - x)) (𝓝[>] x)
      (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).toReal) :=
    by
    -- limit of a helper function, with a small shift compared to `g`
    have :
      tendsto (fun y => (hf.stieltjes_function (y + -1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[>] x)
        (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).toReal) :=
      by
      apply tendsto_apply_add_mul_sq_div_sub (nhds_right'_le_nhds_ne x) hx.2
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply tendsto.mono_left _ nhdsWithin_le_nhds
        have : tendsto (fun y : ℝ => y + -1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + -1 * (x - x) ^ 2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1))
        simpa using this
      · have : Ioo x (x + 1) ∈ 𝓝[>] x := by apply Ioo_mem_nhdsWithin_Ioi;
          exact ⟨le_refl _, by linarith⟩
        filter_upwards [this]
        rintro y ⟨hy : x < y, h'y : y < x + 1⟩
        rw [mem_Ioi]
        nlinarith
    -- apply the sandwiching argument, with the helper function and `g`
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' this hx.2
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : x < y)
      have : 0 < (y - x) ^ 2 := sq_pos_of_pos (sub_pos.2 hy)
      apply div_le_div_of_le_of_nonneg _ (sub_pos.2 hy).le
      exact (sub_le_sub_iff_right _).2 (hf.right_lim_le (by linarith))
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : x < y)
      apply div_le_div_of_le_of_nonneg _ (sub_pos.2 hy).le
      exact (sub_le_sub_iff_right _).2 (hf.le_right_lim (le_refl y))
  -- prove differentiability on the left, by sandwiching with values of `g`
  have L2 :
    tendsto (fun y => (f y - f x) / (y - x)) (𝓝[<] x)
      (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).toReal) :=
    by
    -- limit of a helper function, with a small shift compared to `g`
    have :
      tendsto (fun y => (hf.stieltjes_function (y + -1 * (y - x) ^ 2) - f x) / (y - x)) (𝓝[<] x)
        (𝓝 (rn_deriv hf.stieltjes_function.measure volume x).toReal) :=
      by
      apply tendsto_apply_add_mul_sq_div_sub (nhds_left'_le_nhds_ne x) hx.1
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · apply tendsto.mono_left _ nhdsWithin_le_nhds
        have : tendsto (fun y : ℝ => y + -1 * (y - x) ^ 2) (𝓝 x) (𝓝 (x + -1 * (x - x) ^ 2)) :=
          tendsto_id.add (((tendsto_id.sub_const x).pow 2).const_mul (-1))
        simpa using this
      · have : Ioo (x - 1) x ∈ 𝓝[<] x := by apply Ioo_mem_nhdsWithin_Iio;
          exact ⟨by linarith, le_refl _⟩
        filter_upwards [this]
        rintro y ⟨hy : x - 1 < y, h'y : y < x⟩
        rw [mem_Iio]
        nlinarith
    -- apply the sandwiching argument, with `g` and the helper function
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hx.1 this
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      apply div_le_div_of_nonpos_of_le (sub_neg.2 hy).le
      exact (sub_le_sub_iff_right _).2 (hf.le_right_lim (le_refl _))
    · filter_upwards [self_mem_nhdsWithin]
      rintro y (hy : y < x)
      have : 0 < (y - x) ^ 2 := sq_pos_of_neg (sub_neg.2 hy)
      apply div_le_div_of_nonpos_of_le (sub_neg.2 hy).le
      exact (sub_le_sub_iff_right _).2 (hf.right_lim_le (by linarith))
  -- conclude global differentiability
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, (nhds_left'_sup_nhds_right' x).symm,
    tendsto_sup]
  exact ⟨L2, L1⟩
#align monotone.ae_has_deriv_at Monotone.ae_hasDerivAt

/-- A monotone real function is differentiable Lebesgue-almost everywhere. -/
theorem Monotone.ae_differentiableAt {f : ℝ → ℝ} (hf : Monotone f) : ∀ᵐ x, DifferentiableAt ℝ f x :=
  by filter_upwards [hf.ae_has_deriv_at] with x hx using hx.differentiable_at
#align monotone.ae_differentiable_at Monotone.ae_differentiableAt

/-- A real function which is monotone on a set is differentiable Lebesgue-almost everywhere on
this set. This version does not assume that `s` is measurable. For a formulation with
`volume.restrict s` assuming that `s` is measurable, see `monotone_on.ae_differentiable_within_at`.
-/
theorem MonotoneOn.ae_differentiableWithinAt_of_mem {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s) :
    ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x :=
  by
  /- We use a global monotone extension of `f`, and argue that this extension is differentiable
    almost everywhere. Such an extension need not exist (think of `1/x` on `(0, +∞)`), but it exists
    if one restricts first the function to a compact interval `[a, b]`. -/
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro a b as bs hab
  obtain ⟨g, hg, gf⟩ : ∃ g : ℝ → ℝ, Monotone g ∧ eq_on f g (s ∩ Icc a b) :=
    (hf.mono (inter_subset_left s (Icc a b))).exists_monotone_extension
      (hf.map_bdd_below (inter_subset_left _ _) ⟨a, fun x hx => hx.2.1, as⟩)
      (hf.map_bdd_above (inter_subset_left _ _) ⟨b, fun x hx => hx.2.2, bs⟩)
  filter_upwards [hg.ae_differentiable_at] with x hx
  intro h'x
  apply hx.differentiable_within_at.congr_of_eventually_eq _ (gf ⟨h'x.1, h'x.2.1.le, h'x.2.2.le⟩)
  have : Ioo a b ∈ 𝓝[s] x := nhdsWithin_le_nhds (Ioo_mem_nhds h'x.2.1 h'x.2.2)
  filter_upwards [self_mem_nhdsWithin, this] with y hy h'y
  exact gf ⟨hy, h'y.1.le, h'y.2.le⟩
#align monotone_on.ae_differentiable_within_at_of_mem MonotoneOn.ae_differentiableWithinAt_of_mem

/-- A real function which is monotone on a set is differentiable Lebesgue-almost everywhere on
this set. This version assumes that `s` is measurable and uses `volume.restrict s`.
For a formulation without measurability assumption,
see `monotone_on.ae_differentiable_within_at_of_mem`. -/
theorem MonotoneOn.ae_differentiableWithinAt {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x :=
  by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiable_within_at_of_mem
#align monotone_on.ae_differentiable_within_at MonotoneOn.ae_differentiableWithinAt


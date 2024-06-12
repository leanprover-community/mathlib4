/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Analytic.Basic

#align_import measure_theory.integral.circle_integral from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Integral over a circle in `ℂ`

In this file we define `∮ z in C(c, R), f z` to be the integral $\oint_{|z-c|=|R|} f(z)\,dz$ and
prove some properties of this integral. We give definition and prove most lemmas for a function
`f : ℂ → E`, where `E` is a complex Banach space. For this reason,
some lemmas use, e.g., `(z - c)⁻¹ • f z` instead of `f z / (z - c)`.

## Main definitions

* `circleMap c R`: the exponential map $θ ↦ c + R e^{θi}$;

* `CircleIntegrable f c R`: a function `f : ℂ → E` is integrable on the circle with center `c` and
  radius `R` if `f ∘ circleMap c R` is integrable on `[0, 2π]`;

* `circleIntegral f c R`: the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$;

* `cauchyPowerSeries f c R`: the power series that is equal to
  $\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
  `w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
  series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R`
  and `w` belongs to the corresponding open ball.

## Main statements

* `hasFPowerSeriesOn_cauchy_integral`: for any circle integrable function `f`, the power series
  `cauchyPowerSeries f c R`, `R > 0`, converges to the Cauchy integral
  `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc `Metric.ball c R`;

* `circleIntegral.integral_sub_zpow_of_undef`, `circleIntegral.integral_sub_zpow_of_ne`, and
  `circleIntegral.integral_sub_inv_of_mem_ball`: formulas for `∮ z in C(c, R), (z - w) ^ n`,
  `n : ℤ`. These lemmas cover the following cases:

  - `circleIntegral.integral_sub_zpow_of_undef`, `n < 0` and `|w - c| = |R|`: in this case the
    function is not integrable, so the integral is equal to its default value (zero);

  - `circleIntegral.integral_sub_zpow_of_ne`, `n ≠ -1`: in the cases not covered by the previous
    lemma, we have `(z - w) ^ n = ((z - w) ^ (n + 1) / (n + 1))'`, thus the integral equals zero;

  - `circleIntegral.integral_sub_inv_of_mem_ball`, `n = -1`, `|w - c| < R`: in this case the
    integral is equal to `2πi`.

  The case `n = -1`, `|w -c| > R` is not covered by these lemmas. While it is possible to construct
  an explicit primitive, it is easier to apply Cauchy theorem, so we postpone the proof till we have
  this theorem (see #10000).

## Notation

- `∮ z in C(c, R), f z`: notation for the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$.

## Tags

integral, circle, Cauchy integral
-/


variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open scoped Real NNReal Interval Pointwise Topology

open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics

/-!
### `circleMap`, a parametrization of a circle
-/


/-- The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center
`c` and radius `|R|`. -/
def circleMap (c : ℂ) (R : ℝ) : ℝ → ℂ := fun θ => c + R * exp (θ * I)
#align circle_map circleMap

/-- `circleMap` is `2π`-periodic. -/
theorem periodic_circleMap (c : ℂ) (R : ℝ) : Periodic (circleMap c R) (2 * π) := fun θ => by
  simp [circleMap, add_mul, exp_periodic _]
#align periodic_circle_map periodic_circleMap

theorem Set.Countable.preimage_circleMap {s : Set ℂ} (hs : s.Countable) (c : ℂ) {R : ℝ}
    (hR : R ≠ 0) : (circleMap c R ⁻¹' s).Countable :=
  show (((↑) : ℝ → ℂ) ⁻¹' ((· * I) ⁻¹'
      (exp ⁻¹' ((R * ·) ⁻¹' ((c + ·) ⁻¹' s))))).Countable from
    (((hs.preimage (add_right_injective _)).preimage <|
      mul_right_injective₀ <| ofReal_ne_zero.2 hR).preimage_cexp.preimage <|
        mul_left_injective₀ I_ne_zero).preimage ofReal_injective
#align set.countable.preimage_circle_map Set.Countable.preimage_circleMap

@[simp]
theorem circleMap_sub_center (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ - c = circleMap 0 R θ := by
  simp [circleMap]
#align circle_map_sub_center circleMap_sub_center

theorem circleMap_zero (R θ : ℝ) : circleMap 0 R θ = R * exp (θ * I) :=
  zero_add _
#align circle_map_zero circleMap_zero

@[simp]
theorem abs_circleMap_zero (R : ℝ) (θ : ℝ) : abs (circleMap 0 R θ) = |R| := by simp [circleMap]
#align abs_circle_map_zero abs_circleMap_zero

theorem circleMap_mem_sphere' (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ ∈ sphere c |R| := by simp
#align circle_map_mem_sphere' circleMap_mem_sphere'

theorem circleMap_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    circleMap c R θ ∈ sphere c R := by
  simpa only [_root_.abs_of_nonneg hR] using circleMap_mem_sphere' c R θ
#align circle_map_mem_sphere circleMap_mem_sphere

theorem circleMap_mem_closedBall (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    circleMap c R θ ∈ closedBall c R :=
  sphere_subset_closedBall (circleMap_mem_sphere c hR θ)
#align circle_map_mem_closed_ball circleMap_mem_closedBall

theorem circleMap_not_mem_ball (c : ℂ) (R : ℝ) (θ : ℝ) : circleMap c R θ ∉ ball c R := by
  simp [dist_eq, le_abs_self]
#align circle_map_not_mem_ball circleMap_not_mem_ball

theorem circleMap_ne_mem_ball {c : ℂ} {R : ℝ} {w : ℂ} (hw : w ∈ ball c R) (θ : ℝ) :
    circleMap c R θ ≠ w :=
  (ne_of_mem_of_not_mem hw (circleMap_not_mem_ball _ _ _)).symm
#align circle_map_ne_mem_ball circleMap_ne_mem_ball

/-- The range of `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem range_circleMap (c : ℂ) (R : ℝ) : range (circleMap c R) = sphere c |R| :=
  calc
    range (circleMap c R) = c +ᵥ R • range fun θ : ℝ => exp (θ * I) := by
      simp (config := { unfoldPartialApp := true }) only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, Function.comp_def, real_smul]
    _ = sphere c |R| := by
      rw [Complex.range_exp_mul_I, smul_sphere R 0 zero_le_one]
      simp
#align range_circle_map range_circleMap

/-- The image of `(0, 2π]` under `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem image_circleMap_Ioc (c : ℂ) (R : ℝ) : circleMap c R '' Ioc 0 (2 * π) = sphere c |R| := by
  rw [← range_circleMap, ← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0, zero_add]
#align image_circle_map_Ioc image_circleMap_Ioc

@[simp]
theorem circleMap_eq_center_iff {c : ℂ} {R : ℝ} {θ : ℝ} : circleMap c R θ = c ↔ R = 0 := by
  simp [circleMap, exp_ne_zero]
#align circle_map_eq_center_iff circleMap_eq_center_iff

@[simp]
theorem circleMap_zero_radius (c : ℂ) : circleMap c 0 = const ℝ c :=
  funext fun _ => circleMap_eq_center_iff.2 rfl
#align circle_map_zero_radius circleMap_zero_radius

theorem circleMap_ne_center {c : ℂ} {R : ℝ} (hR : R ≠ 0) {θ : ℝ} : circleMap c R θ ≠ c :=
  mt circleMap_eq_center_iff.1 hR
#align circle_map_ne_center circleMap_ne_center

theorem hasDerivAt_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : ℂ)).const_add c
#align has_deriv_at_circle_map hasDerivAt_circleMap

/- TODO: prove `ContDiff ℝ (circleMap c R)`. This needs a version of `ContDiff.mul`
for multiplication in a normed algebra over the base field. -/
theorem differentiable_circleMap (c : ℂ) (R : ℝ) : Differentiable ℝ (circleMap c R) := fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt
#align differentiable_circle_map differentiable_circleMap

@[continuity]
theorem continuous_circleMap (c : ℂ) (R : ℝ) : Continuous (circleMap c R) :=
  (differentiable_circleMap c R).continuous
#align continuous_circle_map continuous_circleMap

@[measurability]
theorem measurable_circleMap (c : ℂ) (R : ℝ) : Measurable (circleMap c R) :=
  (continuous_circleMap c R).measurable
#align measurable_circle_map measurable_circleMap

@[simp]
theorem deriv_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : deriv (circleMap c R) θ = circleMap 0 R θ * I :=
  (hasDerivAt_circleMap _ _ _).deriv
#align deriv_circle_map deriv_circleMap

theorem deriv_circleMap_eq_zero_iff {c : ℂ} {R : ℝ} {θ : ℝ} :
    deriv (circleMap c R) θ = 0 ↔ R = 0 := by simp [I_ne_zero]
#align deriv_circle_map_eq_zero_iff deriv_circleMap_eq_zero_iff

theorem deriv_circleMap_ne_zero {c : ℂ} {R : ℝ} {θ : ℝ} (hR : R ≠ 0) :
    deriv (circleMap c R) θ ≠ 0 :=
  mt deriv_circleMap_eq_zero_iff.1 hR
#align deriv_circle_map_ne_zero deriv_circleMap_ne_zero

theorem lipschitzWith_circleMap (c : ℂ) (R : ℝ) : LipschitzWith (Real.nnabs R) (circleMap c R) :=
  lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
    NNReal.coe_le_coe.1 <| by simp
#align lipschitz_with_circle_map lipschitzWith_circleMap

theorem continuous_circleMap_inv {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R) :
    Continuous fun θ => (circleMap z R θ - w)⁻¹ := by
  have : ∀ θ, circleMap z R θ - w ≠ 0 := by
    simp_rw [sub_ne_zero]
    exact fun θ => circleMap_ne_mem_ball hw θ
  -- Porting note: was `continuity`
  exact Continuous.inv₀ (by continuity) this
#align continuous_circle_map_inv continuous_circleMap_inv

/-!
### Integrability of a function on a circle
-/


/-- We say that a function `f : ℂ → E` is integrable on the circle with center `c` and radius `R` if
the function `f ∘ circleMap c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circleIntegral` is
`(deriv (circleMap c R) θ) • f (circleMap c R θ)`. Integrability of this function is equivalent
to integrability of `f ∘ circleMap c R` whenever `R ≠ 0`. -/
def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop :=
  IntervalIntegrable (fun θ : ℝ => f (circleMap c R θ)) volume 0 (2 * π)
#align circle_integrable CircleIntegrable

@[simp]
theorem circleIntegrable_const (a : E) (c : ℂ) (R : ℝ) : CircleIntegrable (fun _ => a) c R :=
  intervalIntegrable_const
#align circle_integrable_const circleIntegrable_const

namespace CircleIntegrable

variable {f g : ℂ → E} {c : ℂ} {R : ℝ}

nonrec theorem add (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f + g) c R :=
  hf.add hg
#align circle_integrable.add CircleIntegrable.add

nonrec theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg
#align circle_integrable.neg CircleIntegrable.neg

/-- The function we actually integrate over `[0, 2π]` in the definition of `circleIntegral` is
integrable. -/
theorem out [NormedSpace ℂ E] (hf : CircleIntegrable f c R) :
    IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0
      (2 * π) := by
  simp only [CircleIntegrable, deriv_circleMap, intervalIntegrable_iff] at *
  refine (hf.norm.const_mul |R|).mono' ?_ ?_
  · exact ((continuous_circleMap _ _).aestronglyMeasurable.mul_const I).smul hf.aestronglyMeasurable
  · simp [norm_smul]
#align circle_integrable.out CircleIntegrable.out

end CircleIntegrable

@[simp]
theorem circleIntegrable_zero_radius {f : ℂ → E} {c : ℂ} : CircleIntegrable f c 0 := by
  simp [CircleIntegrable]
#align circle_integrable_zero_radius circleIntegrable_zero_radius

theorem circleIntegrable_iff [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} (R : ℝ) :
    CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π) := by
  by_cases h₀ : R = 0
  · simp (config := { unfoldPartialApp := true }) [h₀, const]
  refine ⟨fun h => h.out, fun h => ?_⟩
  simp only [CircleIntegrable, intervalIntegrable_iff, deriv_circleMap] at h ⊢
  refine (h.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · have H : ∀ {θ}, circleMap 0 R θ * I ≠ 0 := fun {θ} => by simp [h₀, I_ne_zero]
    simpa only [inv_smul_smul₀ H]
      using ((continuous_circleMap 0 R).aestronglyMeasurable.mul_const
        I).aemeasurable.inv.aestronglyMeasurable.smul h.aestronglyMeasurable
  · simp [norm_smul, h₀]
#align circle_integrable_iff circleIntegrable_iff

theorem ContinuousOn.circleIntegrable' {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (sphere c |R|)) : CircleIntegrable f c R :=
  (hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere' _ _)).intervalIntegrable _ _
#align continuous_on.circle_integrable' ContinuousOn.circleIntegrable'

theorem ContinuousOn.circleIntegrable {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c R)) : CircleIntegrable f c R :=
  ContinuousOn.circleIntegrable' <| (_root_.abs_of_nonneg hR).symm ▸ hf
#align continuous_on.circle_integrable ContinuousOn.circleIntegrable

#adaptation_note /-- nightly-2024-04-01: the simpNF linter now times out on this lemma. -/
/-- The function `fun z ↦ (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle with center `c`
and radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to this circle. -/
@[simp, nolint simpNF]
theorem circleIntegrable_sub_zpow_iff {c w : ℂ} {R : ℝ} {n : ℤ} :
    CircleIntegrable (fun z => (z - w) ^ n) c R ↔ R = 0 ∨ 0 ≤ n ∨ w ∉ sphere c |R| := by
  constructor
  · intro h; contrapose! h; rcases h with ⟨hR, hn, hw⟩
    simp only [circleIntegrable_iff R, deriv_circleMap]
    rw [← image_circleMap_Ioc] at hw; rcases hw with ⟨θ, hθ, rfl⟩
    replace hθ : θ ∈ [[0, 2 * π]] := Icc_subset_uIcc (Ioc_subset_Icc_self hθ)
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ Real.two_pi_pos.ne hθ
    set f : ℝ → ℂ := fun θ' => circleMap c R θ' - circleMap c R θ
    have : ∀ᶠ θ' in 𝓝[≠] θ, f θ' ∈ ball (0 : ℂ) 1 \ {0} := by
      suffices ∀ᶠ z in 𝓝[≠] circleMap c R θ, z - circleMap c R θ ∈ ball (0 : ℂ) 1 \ {0} from
        ((differentiable_circleMap c R θ).hasDerivAt.tendsto_punctured_nhds
          (deriv_circleMap_ne_zero hR)).eventually this
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp_all [dist_eq, sub_eq_zero]
    refine (((hasDerivAt_circleMap c R θ).isBigO_sub.mono inf_le_left).inv_rev
      (this.mono fun θ' h₁ h₂ => absurd h₂ h₁.2)).trans ?_
    refine IsBigO.of_bound |R|⁻¹ (this.mono fun θ' hθ' => ?_)
    set x := abs (f θ')
    suffices x⁻¹ ≤ x ^ n by
      simpa only [inv_mul_cancel_left₀, abs_eq_zero.not.2 hR, norm_eq_abs, map_inv₀,
        Algebra.id.smul_eq_mul, map_mul, abs_circleMap_zero, abs_I, mul_one, abs_zpow, Ne,
        not_false_iff] using this
    have : x ∈ Ioo (0 : ℝ) 1 := by simpa [x, and_comm] using hθ'
    rw [← zpow_neg_one]
    refine (zpow_strictAnti this.1 this.2).le_iff_le.2 (Int.lt_add_one_iff.1 ?_); exact hn
  · rintro (rfl | H)
    exacts [circleIntegrable_zero_radius,
      ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz =>
        H.symm.imp_left fun (hw : w ∉ sphere c |R|) =>
          sub_ne_zero.2 <| ne_of_mem_of_not_mem hz hw).circleIntegrable']
#align circle_integrable_sub_zpow_iff circleIntegrable_sub_zpow_iff

#adaptation_note /-- nightly-2024-04-01
The simpNF linter now times out on this lemma. -/
@[simp, nolint simpNF]
theorem circleIntegrable_sub_inv_iff {c w : ℂ} {R : ℝ} :
    CircleIntegrable (fun z => (z - w)⁻¹) c R ↔ R = 0 ∨ w ∉ sphere c |R| := by
  simp only [← zpow_neg_one, circleIntegrable_sub_zpow_iff]; norm_num
#align circle_integrable_sub_inv_iff circleIntegrable_sub_inv_iff

variable [NormedSpace ℂ E] [CompleteSpace E]

/-- Definition for $\oint_{|z-c|=R} f(z)\,dz$. -/
def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in (0)..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)
#align circle_integral circleIntegral

notation3 "∮ "(...)" in ""C("c", "R")"", "r:(scoped f => circleIntegral f c R) => r

theorem circleIntegral_def_Icc (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in Icc 0 (2 * π),
    deriv (circleMap c R) θ • f (circleMap c R θ) := by
  rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]
#align circle_integral_def_Icc circleIntegral_def_Icc

namespace circleIntegral

@[simp]
theorem integral_radius_zero (f : ℂ → E) (c : ℂ) : (∮ z in C(c, 0), f z) = 0 := by
  simp (config := { unfoldPartialApp := true }) [circleIntegral, const]
#align circle_integral.integral_radius_zero circleIntegral.integral_radius_zero

theorem integral_congr {f g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : EqOn f g (sphere c R)) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), g z :=
  intervalIntegral.integral_congr fun θ _ => by simp only [h (circleMap_mem_sphere _ hR _)]
#align circle_integral.integral_congr circleIntegral.integral_congr

theorem integral_sub_inv_smul_sub_smul (f : ℂ → E) (c w : ℂ) (R : ℝ) :
    (∮ z in C(c, R), (z - w)⁻¹ • (z - w) • f z) = ∮ z in C(c, R), f z := by
  rcases eq_or_ne R 0 with (rfl | hR); · simp only [integral_radius_zero]
  have : (circleMap c R ⁻¹' {w}).Countable := (countable_singleton _).preimage_circleMap c hR
  refine intervalIntegral.integral_congr_ae ((this.ae_not_mem _).mono fun θ hθ _' => ?_)
  change circleMap c R θ ≠ w at hθ
  simp only [inv_smul_smul₀ (sub_ne_zero.2 <| hθ)]
#align circle_integral.integral_sub_inv_smul_sub_smul circleIntegral.integral_sub_inv_smul_sub_smul

theorem integral_undef {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) = 0 :=
  intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)
#align circle_integral.integral_undef circleIntegral.integral_undef

theorem integral_sub {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z - g z) = (∮ z in C(c, R), f z) - ∮ z in C(c, R), g z := by
  simp only [circleIntegral, smul_sub, intervalIntegral.integral_sub hf.out hg.out]
#align circle_integral.integral_sub circleIntegral.integral_sub

theorem norm_integral_le_of_norm_le_const' {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hf : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ C) : ‖∮ z in C(c, R), f z‖ ≤ 2 * π * |R| * C :=
  calc
    ‖∮ z in C(c, R), f z‖ ≤ |R| * C * |2 * π - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ = |R| * ‖f (circleMap c R θ)‖ := by
            simp [norm_smul]
          _ ≤ |R| * C :=
            mul_le_mul_of_nonneg_left (hf _ <| circleMap_mem_sphere' _ _ _) (abs_nonneg _)
    _ = 2 * π * |R| * C := by rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]; ac_rfl
#align circle_integral.norm_integral_le_of_norm_le_const' circleIntegral.norm_integral_le_of_norm_le_const'

theorem norm_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) : ‖∮ z in C(c, R), f z‖ ≤ 2 * π * R * C :=
  have : |R| = R := abs_of_nonneg hR
  calc
    ‖∮ z in C(c, R), f z‖ ≤ 2 * π * |R| * C := norm_integral_le_of_norm_le_const' <| by rwa [this]
    _ = 2 * π * R * C := by rw [this]
#align circle_integral.norm_integral_le_of_norm_le_const circleIntegral.norm_integral_le_of_norm_le_const

theorem norm_two_pi_i_inv_smul_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hR : 0 ≤ R) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), f z‖ ≤ R * C := by
  have : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by simp [Real.pi_pos.le]
  rw [norm_smul, this, ← div_eq_inv_mul, div_le_iff Real.two_pi_pos, mul_comm (R * C), ← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf
set_option linter.uppercaseLean3 false in
#align circle_integral.norm_two_pi_I_inv_smul_integral_le_of_norm_le_const circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const

/-- If `f` is continuous on the circle `|z - c| = R`, `R > 0`, the `‖f z‖` is less than or equal to
`C : ℝ` on this circle, and this norm is strictly less than `C` at some point `z` of the circle,
then `‖∮ z in C(c, R), f z‖ < 2 * π * R * C`. -/
theorem norm_integral_lt_of_norm_le_const_of_lt {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hc : ContinuousOn f (sphere c R)) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C)
    (hlt : ∃ z ∈ sphere c R, ‖f z‖ < C) : ‖∮ z in C(c, R), f z‖ < 2 * π * R * C := by
  rw [← _root_.abs_of_pos hR, ← image_circleMap_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc
    ‖∮ z in C(c, R), f z‖ ≤ ∫ θ in (0)..2 * π, ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ < ∫ _ in (0)..2 * π, R * C := by
      simp only [norm_smul, deriv_circleMap, norm_eq_abs, map_mul, abs_I, mul_one,
        abs_circleMap_zero, abs_of_pos hR]
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          Real.two_pi_pos ?_ continuousOn_const (fun θ _ => ?_) ⟨θ₀, Ioc_subset_Icc_self hmem, ?_⟩
      · exact continuousOn_const.mul (hc.comp (continuous_circleMap _ _).continuousOn fun θ _ =>
          circleMap_mem_sphere _ hR.le _).norm
      · exact mul_le_mul_of_nonneg_left (hf _ <| circleMap_mem_sphere _ hR.le _) hR.le
      · exact (mul_lt_mul_left hR).2 hlt
    _ = 2 * π * R * C := by simp [mul_assoc]; ring
#align circle_integral.norm_integral_lt_of_norm_le_const_of_lt circleIntegral.norm_integral_lt_of_norm_le_const_of_lt

@[simp]
theorem integral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 ℂ E] (a : 𝕜)
    (f : ℂ → E) (c : ℂ) (R : ℝ) : (∮ z in C(c, R), a • f z) = a • ∮ z in C(c, R), f z := by
  simp only [circleIntegral, ← smul_comm a (_ : ℂ) (_ : E), intervalIntegral.integral_smul]
#align circle_integral.integral_smul circleIntegral.integral_smul

@[simp]
theorem integral_smul_const (f : ℂ → ℂ) (a : E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z • a) = (∮ z in C(c, R), f z) • a := by
  simp only [circleIntegral, intervalIntegral.integral_smul_const, ← smul_assoc]
#align circle_integral.integral_smul_const circleIntegral.integral_smul_const

@[simp]
theorem integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z :=
  integral_smul a f c R
#align circle_integral.integral_const_mul circleIntegral.integral_const_mul

@[simp]
theorem integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I := by
  simp [circleIntegral, ← div_eq_mul_inv, mul_div_cancel_left₀ _ (circleMap_ne_center hR),
    -- Porting note: `simp` didn't need a hint to apply `integral_const` here
    intervalIntegral.integral_const I]
#align circle_integral.integral_sub_center_inv circleIntegral.integral_sub_center_inv

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`Metric.sphere c |R|`, then `∮ z in C(c, R), f' z = 0`. -/
theorem integral_eq_zero_of_hasDerivWithinAt' {f f' : ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ z ∈ sphere c |R|, HasDerivWithinAt f (f' z) (sphere c |R|) z) :
    (∮ z in C(c, R), f' z) = 0 := by
  by_cases hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circleMap c R).comp f).eq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
    exact (h _ (circleMap_mem_sphere' _ _ _)).scomp_hasDerivAt θ
      (differentiable_circleMap _ _ _).hasDerivAt (circleMap_mem_sphere' _ _)
  · exact integral_undef hi
#align circle_integral.integral_eq_zero_of_has_deriv_within_at' circleIntegral.integral_eq_zero_of_hasDerivWithinAt'

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`Metric.sphere c R`, then `∮ z in C(c, R), f' z = 0`. -/
theorem integral_eq_zero_of_hasDerivWithinAt {f f' : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R, HasDerivWithinAt f (f' z) (sphere c R) z) : (∮ z in C(c, R), f' z) = 0 :=
  integral_eq_zero_of_hasDerivWithinAt' <| (_root_.abs_of_nonneg hR).symm ▸ h
#align circle_integral.integral_eq_zero_of_has_deriv_within_at circleIntegral.integral_eq_zero_of_hasDerivWithinAt

/-- If `n < 0` and `|w - c| = |R|`, then `(z - w) ^ n` is not circle integrable on the circle with
center `c` and radius `|R|`, so the integral `∮ z in C(c, R), (z - w) ^ n` is equal to zero. -/
theorem integral_sub_zpow_of_undef {n : ℤ} {c w : ℂ} {R : ℝ} (hn : n < 0)
    (hw : w ∈ sphere c |R|) : (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases eq_or_ne R 0 with (rfl | h0)
  · apply integral_radius_zero
  · apply integral_undef
    simpa [circleIntegrable_sub_zpow_iff, *, not_or]
#align circle_integral.integral_sub_zpow_of_undef circleIntegral.integral_sub_zpow_of_undef

/-- If `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the circle equals
zero. -/
theorem integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) :
    (∮ z in C(c, R), (z - w) ^ n) = 0 := by
  rcases em (w ∈ sphere c |R| ∧ n < -1) with (⟨hw, hn⟩ | H)
  · exact integral_sub_zpow_of_undef (hn.trans (by decide)) hw
  push_neg at H
  have hd : ∀ z, z ≠ w ∨ -1 ≤ n →
      HasDerivAt (fun z => (z - w) ^ (n + 1) / (n + 1)) ((z - w) ^ n) z := by
    intro z hne
    convert ((hasDerivAt_zpow (n + 1) _ (hne.imp _ _)).comp z
      ((hasDerivAt_id z).sub_const w)).div_const _ using 1
    · have hn' : (n + 1 : ℂ) ≠ 0 := by
        rwa [Ne, ← eq_neg_iff_add_eq_zero, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
      simp [mul_assoc, mul_div_cancel_left₀ _ hn']
    exacts [sub_ne_zero.2, neg_le_iff_add_nonneg.1]
  refine integral_eq_zero_of_hasDerivWithinAt' fun z hz => (hd z ?_).hasDerivWithinAt
  exact (ne_or_eq z w).imp_right fun (h : z = w) => H <| h ▸ hz
#align circle_integral.integral_sub_zpow_of_ne circleIntegral.integral_sub_zpow_of_ne

end circleIntegral

/-- The power series that is equal to
$\frac{1}{2πi}\sum_{n=0}^{\infty}
  \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
`w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R` and
`w` belongs to the corresponding open ball. For any circle integrable function `f`, this power
series converges to the Cauchy integral for `f`. -/
def cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ) : FormalMultilinearSeries ℂ ℂ E := fun n =>
  ContinuousMultilinearMap.mkPiRing ℂ _ <|
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z
#align cauchy_power_series cauchyPowerSeries

theorem cauchyPowerSeries_apply (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) (w : ℂ) :
    (cauchyPowerSeries f c R n fun _ => w) =
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    div_eq_mul_inv, mul_pow, mul_smul, circleIntegral.integral_smul]
  rw [← smul_comm (w ^ n)]
#align cauchy_power_series_apply cauchyPowerSeries_apply

theorem norm_cauchyPowerSeries_le (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) :
    ‖cauchyPowerSeries f c R n‖ ≤
      ((2 * π)⁻¹ * ∫ θ : ℝ in (0)..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n :=
  calc ‖cauchyPowerSeries f c R n‖
    _ = (2 * π)⁻¹ * ‖∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ := by
      simp [cauchyPowerSeries, norm_smul, Real.pi_pos.le]
    _ ≤ (2 * π)⁻¹ * ∫ θ in (0)..2 * π, ‖deriv (circleMap c R) θ •
        (circleMap c R θ - c)⁻¹ ^ n • (circleMap c R θ - c)⁻¹ • f (circleMap c R θ)‖ :=
      (mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
        (by simp [Real.pi_pos.le]))
    _ = (2 * π)⁻¹ *
        (|R|⁻¹ ^ n * (|R| * (|R|⁻¹ * ∫ x : ℝ in (0)..2 * π, ‖f (circleMap c R x)‖))) := by
      simp [norm_smul, mul_left_comm |R|]
    _ ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in (0)..2 * π, ‖f (circleMap c R θ)‖) * |R|⁻¹ ^ n := by
      rcases eq_or_ne R 0 with (rfl | hR)
      · cases n <;> simp [-mul_inv_rev]
        rw [← mul_assoc, inv_mul_cancel (Real.two_pi_pos.ne.symm), one_mul]
        apply norm_nonneg
      · rw [mul_inv_cancel_left₀, mul_assoc, mul_comm (|R|⁻¹ ^ n)]
        rwa [Ne, _root_.abs_eq_zero]
#align norm_cauchy_power_series_le norm_cauchyPowerSeries_le

theorem le_radius_cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ≥0) :
    ↑R ≤ (cauchyPowerSeries f c R).radius := by
  refine
    (cauchyPowerSeries f c R).le_radius_of_bound
      ((2 * π)⁻¹ * ∫ θ : ℝ in (0)..2 * π, ‖f (circleMap c R θ)‖) fun n => ?_
  refine (mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le _ _ _ _)
    (pow_nonneg R.coe_nonneg _)).trans ?_
  rw [_root_.abs_of_nonneg R.coe_nonneg]
  rcases eq_or_ne (R ^ n : ℝ) 0 with hR | hR
  · rw_mod_cast [hR, mul_zero]
    exact mul_nonneg (inv_nonneg.2 Real.two_pi_pos.le)
      (intervalIntegral.integral_nonneg Real.two_pi_pos.le fun _ _ => norm_nonneg _)
  · rw [inv_pow]
    have : (R:ℝ) ^ n ≠ 0 := by norm_cast at hR ⊢
    rw [inv_mul_cancel_right₀ this]
#align le_radius_cauchy_power_series le_radius_cauchyPowerSeries

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R` multiplied
by `2πI` converges to the integral `∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc
`Metric.ball c R`. -/
theorem hasSum_two_pi_I_cauchyPowerSeries_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : abs w < R) :
    HasSum (fun n : ℕ => ∮ z in C(c, R), (w / (z - c)) ^ n • (z - c)⁻¹ • f z)
      (∮ z in C(c, R), (z - (c + w))⁻¹ • f z) := by
  have hR : 0 < R := (Complex.abs.nonneg w).trans_lt hw
  have hwR : abs w / R ∈ Ico (0 : ℝ) 1 :=
    ⟨div_nonneg (Complex.abs.nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (abs w / R) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [AEStronglyMeasurable.smul, hf.def'.1] <;> apply Measurable.aestronglyMeasurable
    -- Porting note: these were `measurability`
    · exact (measurable_circleMap 0 R).mul_const I
    · exact (((measurable_circleMap c R).sub measurable_const).const_div w).pow measurable_const
    · exact ((measurable_circleMap c R).sub measurable_const).inv
  · simp [norm_smul, abs_of_pos hR, mul_left_comm R, inv_mul_cancel_left₀ hR.ne', mul_comm ‖_‖]
  · exact eventually_of_forall fun _ _ => (summable_geometric_of_lt_one hwR.1 hwR.2).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hwR.1 hwR.2] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine eventually_of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have : ‖w / (circleMap c R θ - c)‖ < 1 := by simpa [abs_of_pos hR] using hwR.2
    convert (hasSum_geometric_of_norm_lt_one this).mul_right _ using 1
    simp [← sub_sub, ← mul_inv, sub_mul, div_mul_cancel₀ _ (circleMap_ne_center hR.ne')]
set_option linter.uppercaseLean3 false in
#align has_sum_two_pi_I_cauchy_power_series_integral hasSum_two_pi_I_cauchyPowerSeries_integral

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
theorem hasSum_cauchyPowerSeries_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : abs w < R) :
    HasSum (fun n => cauchyPowerSeries f c R n fun _ => w)
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z) := by
  simp only [cauchyPowerSeries_apply]
  exact (hasSum_two_pi_I_cauchyPowerSeries_integral hf hw).const_smul _
#align has_sum_cauchy_power_series_integral hasSum_cauchyPowerSeries_integral

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
theorem sum_cauchyPowerSeries_eq_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : abs w < R) :
    (cauchyPowerSeries f c R).sum w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - (c + w))⁻¹ • f z :=
  (hasSum_cauchyPowerSeries_integral hf hw).tsum_eq
#align sum_cauchy_power_series_eq_integral sum_cauchyPowerSeries_eq_integral

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
theorem hasFPowerSeriesOn_cauchy_integral {f : ℂ → E} {c : ℂ} {R : ℝ≥0}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    HasFPowerSeriesOnBall (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z)
      (cauchyPowerSeries f c R) c R :=
  { r_le := le_radius_cauchyPowerSeries _ _ _
    r_pos := ENNReal.coe_pos.2 hR
    hasSum := fun hy ↦ hasSum_cauchyPowerSeries_integral hf <| by simpa using hy }
#align has_fpower_series_on_cauchy_integral hasFPowerSeriesOn_cauchy_integral

namespace circleIntegral

/-- Integral $\oint_{|z-c|=R} \frac{dz}{z-w} = 2πi$ whenever $|w-c| < R$. -/
theorem integral_sub_inv_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : ℕ => ∮ z in C(c, R), ((w - c) / (z - c)) ^ n * (z - c)⁻¹)
      (2 * π * I) by
    have A : CircleIntegrable (fun _ => (1 : ℂ)) c R := continuousOn_const.circleIntegrable'
    refine (H.unique ?_).symm
    simpa only [smul_eq_mul, mul_one, add_sub_cancel] using
      hasSum_two_pi_I_cauchyPowerSeries_integral A hw
  have H : ∀ n : ℕ, n ≠ 0 → (∮ z in C(c, R), (z - c) ^ (-n - 1 : ℤ)) = 0 := by
    refine fun n hn => integral_sub_zpow_of_ne ?_ _ _ _; simpa
  have : (∮ z in C(c, R), ((w - c) / (z - c)) ^ 0 * (z - c)⁻¹) = 2 * π * I := by simp [hR.ne']
  refine this ▸ hasSum_single _ fun n hn => ?_
  simp only [div_eq_mul_inv, mul_pow, integral_const_mul, mul_assoc]
  rw [(integral_congr hR.le fun z hz => _).trans (H n hn), mul_zero]
  intro z _
  rw [← pow_succ, ← zpow_natCast, inv_zpow, ← zpow_neg, Int.ofNat_succ, neg_add,
    sub_eq_add_neg _ (1 : ℤ)]
#align circle_integral.integral_sub_inv_of_mem_ball circleIntegral.integral_sub_inv_of_mem_ball

end circleIntegral

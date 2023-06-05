/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.integral.vitali_caratheodory
! leanprover-community/mathlib commit 57ac39bd365c2f80589a700f9fbb664d3a1a30c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.Topology.Semicontinuous
import Mathbin.MeasureTheory.Integral.Bochner
import Mathbin.Topology.Instances.Ereal

/-!
# Vitali-Carathéodory theorem

Vitali-Carathéodory theorem asserts the following. Consider an integrable function `f : α → ℝ` on
a space with a regular measure. Then there exists a function `g : α → ereal` such that `f x < g x`
everywhere, `g` is lower semicontinuous, and the integral of `g` is arbitrarily close to that of
`f`. This theorem is proved in this file, as `exists_lt_lower_semicontinuous_integral_lt`.

Symmetrically, there exists `g < f` which is upper semicontinuous, with integral arbitrarily close
to that of `f`. It follows from the previous statement applied to `-f`. It is formalized under
the name `exists_upper_semicontinuous_lt_integral_gt`.

The most classical version of Vitali-Carathéodory theorem only ensures a large inequality
`f x ≤ g x`. For applications to the fundamental theorem of calculus, though, the strict inequality
`f x < g x` is important. Therefore, we prove the stronger version with strict inequalities in this
file. There is a price to pay: we require that the measure is `σ`-finite, which is not necessary for
the classical Vitali-Carathéodory theorem. Since this is satisfied in all applications, this is
not a real problem.

## Sketch of proof

Decomposing `f` as the difference of its positive and negative parts, it suffices to show that a
positive function can be bounded from above by a lower semicontinuous function, and from below
by an upper semicontinuous function, with integrals close to that of `f`.

For the bound from above, write `f` as a series `∑' n, cₙ * indicator (sₙ)` of simple functions.
Then, approximate `sₙ` by a larger open set `uₙ` with measure very close to that of `sₙ` (this is
possible by regularity of the measure), and set `g = ∑' n, cₙ * indicator (uₙ)`. It is
lower semicontinuous as a series of lower semicontinuous functions, and its integral is arbitrarily
close to that of `f`.

For the bound from below, use finitely many terms in the series, and approximate `sₙ` from inside by
a closed set `Fₙ`. Then `∑ n < N, cₙ * indicator (Fₙ)` is bounded from above by `f`, it is
upper semicontinuous as a finite sum of upper semicontinuous functions, and its integral is
arbitrarily close to that of `f`.

The main pain point in the implementation is that one needs to jump between the spaces `ℝ`, `ℝ≥0`,
`ℝ≥0∞` and `ereal` (and be careful that addition is not well behaved on `ereal`), and between
`lintegral` and `integral`.

We first show the bound from above for simple functions and the nonnegative integral
(this is the main nontrivial mathematical point), then deduce it for general nonnegative functions,
first for the nonnegative integral and then for the Bochner integral.

Then we follow the same steps for the lower bound.

Finally, we glue them together to obtain the main statement
`exists_lt_lower_semicontinuous_integral_lt`.

## Related results

Are you looking for a result on approximation by continuous functions (not just semicontinuous)?
See result `measure_theory.Lp.continuous_map_dense`, in the file
`measure_theory.continuous_map_dense`.

## References

[Rudin, *Real and Complex Analysis* (Theorem 2.24)][rudin2006real]

-/


open scoped ENNReal NNReal

open MeasureTheory MeasureTheory.Measure

variable {α : Type _} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] (μ : Measure α)
  [WeaklyRegular μ]

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

/-! ### Lower semicontinuous upper bound for nonnegative functions -/


/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊇ » s) -/
/-- Given a simple function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge (f : α →ₛ ℝ≥0) {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  induction' f using MeasureTheory.SimpleFunc.induction with c s hs f₁ f₂ H h₁ h₂ generalizing ε
  · let f := simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)
    by_cases h : (∫⁻ x, f x ∂μ) = ⊤
    · refine'
        ⟨fun x => c, fun x => _, lowerSemicontinuous_const, by
          simp only [_root_.top_add, le_top, h]⟩
      simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        Set.piecewise_eq_indicator, simple_func.coe_piecewise]
      exact Set.indicator_le_self _ _ _
    by_cases hc : c = 0
    · refine' ⟨fun x => 0, _, lowerSemicontinuous_const, _⟩
      ·
        simp only [hc, Set.indicator_zero', Pi.zero_apply, simple_func.const_zero, imp_true_iff,
          eq_self_iff_true, simple_func.coe_zero, Set.piecewise_eq_indicator,
          simple_func.coe_piecewise, le_zero_iff]
      · simp only [lintegral_const, MulZeroClass.zero_mul, zero_le, ENNReal.coe_zero]
    have : μ s < μ s + ε / c :=
      by
      have : (0 : ℝ≥0∞) < ε / c := ENNReal.div_pos_iff.2 ⟨ε0, ENNReal.coe_ne_top⟩
      simpa using ENNReal.add_lt_add_left _ this
      simpa only [hs, hc, lt_top_iff_ne_top, true_and_iff, simple_func.coe_const,
        Function.const_apply, lintegral_const, ENNReal.coe_indicator, Set.univ_inter,
        ENNReal.coe_ne_top, MeasurableSet.univ, WithTop.mul_eq_top_iff, simple_func.const_zero,
        or_false_iff, lintegral_indicator, ENNReal.coe_eq_zero, Ne.def, not_false_iff,
        simple_func.coe_zero, Set.piecewise_eq_indicator, simple_func.coe_piecewise, false_and_iff,
        restrict_apply] using h
    obtain ⟨u, su, u_open, μu⟩ : ∃ (u : _) (_ : u ⊇ s), IsOpen u ∧ μ u < μ s + ε / c :=
      s.exists_is_open_lt_of_lt _ this
    refine'
      ⟨Set.indicator u fun x => c, fun x => _, u_open.lower_semicontinuous_indicator (zero_le _), _⟩
    · simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        Set.piecewise_eq_indicator, simple_func.coe_piecewise]
      exact Set.indicator_le_indicator_of_subset su (fun x => zero_le _) _
    · suffices (c : ℝ≥0∞) * μ u ≤ c * μ s + ε by
        simpa only [hs, u_open.measurable_set, simple_func.coe_const, Function.const_apply,
          lintegral_const, ENNReal.coe_indicator, Set.univ_inter, MeasurableSet.univ,
          simple_func.const_zero, lintegral_indicator, simple_func.coe_zero,
          Set.piecewise_eq_indicator, simple_func.coe_piecewise, restrict_apply]
      calc
        (c : ℝ≥0∞) * μ u ≤ c * (μ s + ε / c) := mul_le_mul_left' μu.le _
        _ = c * μ s + ε := by
          simp_rw [mul_add]
          rw [ENNReal.mul_div_cancel' _ ENNReal.coe_ne_top]
          simpa using hc
        
  · rcases h₁ (ENNReal.half_pos ε0).ne' with ⟨g₁, f₁_le_g₁, g₁cont, g₁int⟩
    rcases h₂ (ENNReal.half_pos ε0).ne' with ⟨g₂, f₂_le_g₂, g₂cont, g₂int⟩
    refine'
      ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, _⟩
    simp only [simple_func.coe_add, ENNReal.coe_add, Pi.add_apply]
    rw [lintegral_add_left f₁.measurable.coe_nnreal_ennreal,
      lintegral_add_left g₁cont.measurable.coe_nnreal_ennreal]
    convert add_le_add g₁int g₂int using 1
    simp only
    conv_lhs => rw [← ENNReal.add_halves ε]
    abel
#align measure_theory.simple_func.exists_le_lower_semicontinuous_lintegral_ge MeasureTheory.SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge

open SimpleFunc (eapproxDiff tsum_eapproxDiff)

/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_le_lowerSemicontinuous_lintegral_ge (f : α → ℝ≥0∞) (hf : Measurable f) {ε : ℝ≥0∞}
    (εpos : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, f x ≤ g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  rcases ENNReal.exists_pos_sum_of_countable' εpos ℕ with ⟨δ, δpos, hδ⟩
  have :
    ∀ n,
      ∃ g : α → ℝ≥0,
        (∀ x, simple_func.eapprox_diff f n x ≤ g x) ∧
          LowerSemicontinuous g ∧
            (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, simple_func.eapprox_diff f n x ∂μ) + δ n :=
    fun n =>
    simple_func.exists_le_lower_semicontinuous_lintegral_ge μ (simple_func.eapprox_diff f n)
      (δpos n).ne'
  choose g f_le_g gcont hg using this
  refine' ⟨fun x => ∑' n, g n x, fun x => _, _, _⟩
  · rw [← tsum_eapprox_diff f hf]
    exact ENNReal.tsum_le_tsum fun n => ENNReal.coe_le_coe.2 (f_le_g n x)
  · apply lowerSemicontinuous_tsum fun n => _
    exact
      ennreal.continuous_coe.comp_lower_semicontinuous (gcont n) fun x y hxy =>
        ENNReal.coe_le_coe.2 hxy
  ·
    calc
      (∫⁻ x, ∑' n : ℕ, g n x ∂μ) = ∑' n, ∫⁻ x, g n x ∂μ := by
        rw [lintegral_tsum fun n => (gcont n).Measurable.coe_nnreal_ennreal.AEMeasurable]
      _ ≤ ∑' n, (∫⁻ x, eapprox_diff f n x ∂μ) + δ n := (ENNReal.tsum_le_tsum hg)
      _ = (∑' n, ∫⁻ x, eapprox_diff f n x ∂μ) + ∑' n, δ n := ENNReal.tsum_add
      _ ≤ (∫⁻ x : α, f x ∂μ) + ε := by
        refine' add_le_add _ hδ.le
        rw [← lintegral_tsum]
        · simp_rw [tsum_eapprox_diff f hf, le_refl]
        · intro n; exact (simple_func.measurable _).coe_nnreal_ennreal.AEMeasurable
      
#align measure_theory.exists_le_lower_semicontinuous_lintegral_ge MeasureTheory.exists_le_lowerSemicontinuous_lintegral_ge

/-- Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lowerSemicontinuous_lintegral_ge [SigmaFinite μ] (f : α → ℝ≥0)
    (fmeas : Measurable f) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  have : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
  rcases exists_pos_lintegral_lt_of_sigma_finite μ this with ⟨w, wpos, wmeas, wint⟩
  let f' x := ((f x + w x : ℝ≥0) : ℝ≥0∞)
  rcases exists_le_lower_semicontinuous_lintegral_ge μ f' (fmeas.add wmeas).coe_nnreal_ennreal
      this with
    ⟨g, le_g, gcont, gint⟩
  refine' ⟨g, fun x => _, gcont, _⟩
  ·
    calc
      (f x : ℝ≥0∞) < f' x := by simpa [← ENNReal.coe_lt_coe] using add_lt_add_left (wpos x) (f x)
      _ ≤ g x := le_g x
      
  ·
    calc
      (∫⁻ x : α, g x ∂μ) ≤ (∫⁻ x : α, f x + w x ∂μ) + ε / 2 := gint
      _ = ((∫⁻ x : α, f x ∂μ) + ∫⁻ x : α, w x ∂μ) + ε / 2 := by
        rw [lintegral_add_right _ wmeas.coe_nnreal_ennreal]
      _ ≤ (∫⁻ x : α, f x ∂μ) + ε / 2 + ε / 2 := (add_le_add_right (add_le_add_left wint.le _) _)
      _ = (∫⁻ x : α, f x ∂μ) + ε := by rw [add_assoc, ENNReal.add_halves]
      
#align measure_theory.exists_lt_lower_semicontinuous_lintegral_ge MeasureTheory.exists_lt_lowerSemicontinuous_lintegral_ge

/-- Given an almost everywhere measurable function `f` with values in `ℝ≥0` in a sigma-finite space,
there exists a lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lowerSemicontinuous_lintegral_ge_of_aEMeasurable [SigmaFinite μ] (f : α → ℝ≥0)
    (fmeas : AEMeasurable f μ) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧ LowerSemicontinuous g ∧ (∫⁻ x, g x ∂μ) ≤ (∫⁻ x, f x ∂μ) + ε :=
  by
  have : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
  rcases exists_lt_lower_semicontinuous_lintegral_ge μ (fmeas.mk f) fmeas.measurable_mk this with
    ⟨g0, f_lt_g0, g0_cont, g0_int⟩
  rcases exists_measurable_superset_of_null fmeas.ae_eq_mk with ⟨s, hs, smeas, μs⟩
  rcases exists_le_lower_semicontinuous_lintegral_ge μ (s.indicator fun x => ∞)
      (measurable_const.indicator smeas) this with
    ⟨g1, le_g1, g1_cont, g1_int⟩
  refine' ⟨fun x => g0 x + g1 x, fun x => _, g0_cont.add g1_cont, _⟩
  · by_cases h : x ∈ s
    · have := le_g1 x
      simp only [h, Set.indicator_of_mem, top_le_iff] at this 
      simp [this]
    · have : f x = fmeas.mk f x := by rw [Set.compl_subset_comm] at hs ; exact hs h
      rw [this]
      exact (f_lt_g0 x).trans_le le_self_add
  ·
    calc
      (∫⁻ x, g0 x + g1 x ∂μ) = (∫⁻ x, g0 x ∂μ) + ∫⁻ x, g1 x ∂μ :=
        lintegral_add_left g0_cont.measurable _
      _ ≤ (∫⁻ x, f x ∂μ) + ε / 2 + (0 + ε / 2) :=
        by
        refine' add_le_add _ _
        · convert g0_int using 2
          exact lintegral_congr_ae (fmeas.ae_eq_mk.fun_comp _)
        · convert g1_int
          simp only [smeas, μs, lintegral_const, Set.univ_inter, MeasurableSet.univ,
            lintegral_indicator, MulZeroClass.mul_zero, restrict_apply]
      _ = (∫⁻ x, f x ∂μ) + ε := by simp only [add_assoc, ENNReal.add_halves, zero_add]
      
#align measure_theory.exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable MeasureTheory.exists_lt_lowerSemicontinuous_lintegral_ge_of_aEMeasurable

variable {μ}

/-- Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lowerSemicontinuous_integral_gt_nNReal [SigmaFinite μ] (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0∞,
      (∀ x, (f x : ℝ≥0∞) < g x) ∧
        LowerSemicontinuous g ∧
          (∀ᵐ x ∂μ, g x < ⊤) ∧
            Integrable (fun x => (g x).toReal) μ ∧ (∫ x, (g x).toReal ∂μ) < (∫ x, f x ∂μ) + ε :=
  by
  have fmeas : AEMeasurable f μ :=
    by
    convert fint.ae_strongly_measurable.real_to_nnreal.ae_measurable; ext1 x
    simp only [Real.toNNReal_coe]
  lift ε to ℝ≥0 using εpos.le
  obtain ⟨δ, δpos, hδε⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < ε; exact exists_between εpos
  have int_f_ne_top : (∫⁻ a : α, f a ∂μ) ≠ ∞ :=
    (has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral).Ne
  rcases exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable μ f fmeas
      (ENNReal.coe_ne_zero.2 δpos.ne') with
    ⟨g, f_lt_g, gcont, gint⟩
  have gint_ne : (∫⁻ x : α, g x ∂μ) ≠ ∞ := ne_top_of_le_ne_top (by simpa) gint
  have g_lt_top : ∀ᵐ x : α ∂μ, g x < ∞ := ae_lt_top gcont.measurable gint_ne
  have Ig : (∫⁻ a : α, ENNReal.ofReal (g a).toReal ∂μ) = ∫⁻ a : α, g a ∂μ :=
    by
    apply lintegral_congr_ae
    filter_upwards [g_lt_top] with _ hx
    simp only [hx.ne, ENNReal.ofReal_toReal, Ne.def, not_false_iff]
  refine' ⟨g, f_lt_g, gcont, g_lt_top, _, _⟩
  · refine' ⟨gcont.measurable.ennreal_to_real.ae_measurable.ae_strongly_measurable, _⟩
    simp only [has_finite_integral_iff_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    convert gint_ne.lt_top using 1
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    ·
      calc
        ENNReal.toReal (∫⁻ a : α, ENNReal.ofReal (g a).toReal ∂μ) =
            ENNReal.toReal (∫⁻ a : α, g a ∂μ) :=
          by congr 1
        _ ≤ ENNReal.toReal ((∫⁻ a : α, f a ∂μ) + δ) :=
          by
          apply ENNReal.toReal_mono _ gint
          simpa using int_f_ne_top
        _ = ENNReal.toReal (∫⁻ a : α, f a ∂μ) + δ := by
          rw [ENNReal.toReal_add int_f_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal]
        _ < ENNReal.toReal (∫⁻ a : α, f a ∂μ) + ε := (add_lt_add_left hδε _)
        _ = (∫⁻ a : α, ENNReal.ofReal ↑(f a) ∂μ).toReal + ε := by simp
        
    · apply Filter.eventually_of_forall fun x => _; simp
    · exact fmeas.coe_nnreal_real.ae_strongly_measurable
    · apply Filter.eventually_of_forall fun x => _; simp
    · apply gcont.measurable.ennreal_to_real.ae_measurable.ae_strongly_measurable
#align measure_theory.exists_lt_lower_semicontinuous_integral_gt_nnreal MeasureTheory.exists_lt_lowerSemicontinuous_integral_gt_nNReal

/-! ### Upper semicontinuous lower bound for nonnegative functions -/


/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (F «expr ⊆ » s) -/
/-- Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem SimpleFunc.exists_upperSemicontinuous_le_lintegral_le (f : α →ₛ ℝ≥0)
    (int_f : (∫⁻ x, f x ∂μ) ≠ ∞) {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧ (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, g x ∂μ) + ε :=
  by
  induction' f using MeasureTheory.SimpleFunc.induction with c s hs f₁ f₂ H h₁ h₂ generalizing ε
  · let f := simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)
    by_cases hc : c = 0
    · refine' ⟨fun x => 0, _, upperSemicontinuous_const, _⟩
      ·
        simp only [hc, Set.indicator_zero', Pi.zero_apply, simple_func.const_zero, imp_true_iff,
          eq_self_iff_true, simple_func.coe_zero, Set.piecewise_eq_indicator,
          simple_func.coe_piecewise, le_zero_iff]
      ·
        simp only [hc, Set.indicator_zero', lintegral_const, MulZeroClass.zero_mul, Pi.zero_apply,
          simple_func.const_zero, zero_add, zero_le', simple_func.coe_zero,
          Set.piecewise_eq_indicator, ENNReal.coe_zero, simple_func.coe_piecewise, zero_le]
    have μs_lt_top : μ s < ∞ := by
      simpa only [hs, hc, lt_top_iff_ne_top, true_and_iff, simple_func.coe_const, or_false_iff,
        lintegral_const, ENNReal.coe_indicator, Set.univ_inter, ENNReal.coe_ne_top,
        restrict_apply MeasurableSet.univ, WithTop.mul_eq_top_iff, simple_func.const_zero,
        Function.const_apply, lintegral_indicator, ENNReal.coe_eq_zero, Ne.def, not_false_iff,
        simple_func.coe_zero, Set.piecewise_eq_indicator, simple_func.coe_piecewise,
        false_and_iff] using int_f
    have : (0 : ℝ≥0∞) < ε / c := ENNReal.div_pos_iff.2 ⟨ε0, ENNReal.coe_ne_top⟩
    obtain ⟨F, Fs, F_closed, μF⟩ : ∃ (F : _) (_ : F ⊆ s), IsClosed F ∧ μ s < μ F + ε / c :=
      hs.exists_is_closed_lt_add μs_lt_top.ne this.ne'
    refine'
      ⟨Set.indicator F fun x => c, fun x => _, F_closed.upper_semicontinuous_indicator (zero_le _),
        _⟩
    · simp only [simple_func.coe_const, simple_func.const_zero, simple_func.coe_zero,
        Set.piecewise_eq_indicator, simple_func.coe_piecewise]
      exact Set.indicator_le_indicator_of_subset Fs (fun x => zero_le _) _
    · suffices (c : ℝ≥0∞) * μ s ≤ c * μ F + ε by
        simpa only [hs, F_closed.measurable_set, simple_func.coe_const, Function.const_apply,
          lintegral_const, ENNReal.coe_indicator, Set.univ_inter, MeasurableSet.univ,
          simple_func.const_zero, lintegral_indicator, simple_func.coe_zero,
          Set.piecewise_eq_indicator, simple_func.coe_piecewise, restrict_apply]
      calc
        (c : ℝ≥0∞) * μ s ≤ c * (μ F + ε / c) := mul_le_mul_left' μF.le _
        _ = c * μ F + ε := by
          simp_rw [mul_add]
          rw [ENNReal.mul_div_cancel' _ ENNReal.coe_ne_top]
          simpa using hc
        
  · have A : ((∫⁻ x : α, f₁ x ∂μ) + ∫⁻ x : α, f₂ x ∂μ) ≠ ⊤ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    rcases h₁ (ENNReal.add_ne_top.1 A).1 (ENNReal.half_pos ε0).ne' with
      ⟨g₁, f₁_le_g₁, g₁cont, g₁int⟩
    rcases h₂ (ENNReal.add_ne_top.1 A).2 (ENNReal.half_pos ε0).ne' with
      ⟨g₂, f₂_le_g₂, g₂cont, g₂int⟩
    refine'
      ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, _⟩
    simp only [simple_func.coe_add, ENNReal.coe_add, Pi.add_apply]
    rw [lintegral_add_left f₁.measurable.coe_nnreal_ennreal,
      lintegral_add_left g₁cont.measurable.coe_nnreal_ennreal]
    convert add_le_add g₁int g₂int using 1
    simp only
    conv_lhs => rw [← ENNReal.add_halves ε]
    abel
#align measure_theory.simple_func.exists_upper_semicontinuous_le_lintegral_le MeasureTheory.SimpleFunc.exists_upperSemicontinuous_le_lintegral_le

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_upperSemicontinuous_le_lintegral_le (f : α → ℝ≥0) (int_f : (∫⁻ x, f x ∂μ) ≠ ∞)
    {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
    ∃ g : α → ℝ≥0, (∀ x, g x ≤ f x) ∧ UpperSemicontinuous g ∧ (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, g x ∂μ) + ε :=
  by
  obtain ⟨fs, fs_le_f, int_fs⟩ :
    ∃ fs : α →ₛ ℝ≥0, (∀ x, fs x ≤ f x) ∧ (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, fs x ∂μ) + ε / 2 :=
    by
    have := ENNReal.lt_add_right int_f (ENNReal.half_pos ε0).ne'
    conv_rhs at this => rw [lintegral_eq_nnreal (fun x => (f x : ℝ≥0∞)) μ]
    erw [ENNReal.biSup_add] at this  <;> [skip; exact ⟨0, fun x => by simp⟩]
    simp only [lt_iSup_iff] at this 
    rcases this with ⟨fs, fs_le_f, int_fs⟩
    refine' ⟨fs, fun x => by simpa only [ENNReal.coe_le_coe] using fs_le_f x, _⟩
    convert int_fs.le
    rw [← simple_func.lintegral_eq_lintegral]
    rfl
  have int_fs_lt_top : (∫⁻ x, fs x ∂μ) ≠ ∞ :=
    by
    apply ne_top_of_le_ne_top int_f (lintegral_mono fun x => _)
    simpa only [ENNReal.coe_le_coe] using fs_le_f x
  obtain ⟨g, g_le_fs, gcont, gint⟩ :
    ∃ g : α → ℝ≥0,
      (∀ x, g x ≤ fs x) ∧ UpperSemicontinuous g ∧ (∫⁻ x, fs x ∂μ) ≤ (∫⁻ x, g x ∂μ) + ε / 2 :=
    fs.exists_upper_semicontinuous_le_lintegral_le int_fs_lt_top (ENNReal.half_pos ε0).ne'
  refine' ⟨g, fun x => (g_le_fs x).trans (fs_le_f x), gcont, _⟩
  calc
    (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, fs x ∂μ) + ε / 2 := int_fs
    _ ≤ (∫⁻ x, g x ∂μ) + ε / 2 + ε / 2 := (add_le_add gint le_rfl)
    _ = (∫⁻ x, g x ∂μ) + ε := by rw [add_assoc, ENNReal.add_halves]
    
#align measure_theory.exists_upper_semicontinuous_le_lintegral_le MeasureTheory.exists_upperSemicontinuous_le_lintegral_le

/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_upperSemicontinuous_le_integral_le (f : α → ℝ≥0)
    (fint : Integrable (fun x => (f x : ℝ)) μ) {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → ℝ≥0,
      (∀ x, g x ≤ f x) ∧
        UpperSemicontinuous g ∧
          Integrable (fun x => (g x : ℝ)) μ ∧ (∫ x, (f x : ℝ) ∂μ) - ε ≤ ∫ x, g x ∂μ :=
  by
  lift ε to ℝ≥0 using εpos.le
  rw [NNReal.coe_pos, ← ENNReal.coe_pos] at εpos 
  have If : (∫⁻ x, f x ∂μ) < ∞ := has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral
  rcases exists_upper_semicontinuous_le_lintegral_le f If.ne εpos.ne' with ⟨g, gf, gcont, gint⟩
  have Ig : (∫⁻ x, g x ∂μ) < ∞ :=
    by
    apply lt_of_le_of_lt (lintegral_mono fun x => _) If
    simpa using gf x
  refine' ⟨g, gf, gcont, _, _⟩
  · refine'
      integrable.mono fint gcont.measurable.coe_nnreal_real.ae_measurable.ae_strongly_measurable _
    exact Filter.eventually_of_forall fun x => by simp [gf x]
  · rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
    · rw [sub_le_iff_le_add]
      convert ENNReal.toReal_mono _ gint
      · simp
      · rw [ENNReal.toReal_add Ig.ne ENNReal.coe_ne_top]; simp
      · simpa using Ig.ne
    · apply Filter.eventually_of_forall; simp
    · exact gcont.measurable.coe_nnreal_real.ae_measurable.ae_strongly_measurable
    · apply Filter.eventually_of_forall; simp
    · exact fint.ae_strongly_measurable
#align measure_theory.exists_upper_semicontinuous_le_integral_le MeasureTheory.exists_upperSemicontinuous_le_integral_le

/-! ### Vitali-Carathéodory theorem -/


/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g > f` which is lower semicontinuous, with integral arbitrarily close
to that of `f`. This function has to be `ereal`-valued in general. -/
theorem exists_lt_lowerSemicontinuous_integral_lt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → EReal,
      (∀ x, (f x : EReal) < g x) ∧
        LowerSemicontinuous g ∧
          Integrable (fun x => EReal.toReal (g x)) μ ∧
            (∀ᵐ x ∂μ, g x < ⊤) ∧ (∫ x, EReal.toReal (g x) ∂μ) < (∫ x, f x ∂μ) + ε :=
  by
  let δ : ℝ≥0 := ⟨ε / 2, (half_pos εpos).le⟩
  have δpos : 0 < δ := half_pos εpos
  let fp : α → ℝ≥0 := fun x => Real.toNNReal (f x)
  have int_fp : integrable (fun x => (fp x : ℝ)) μ := hf.real_to_nnreal
  rcases exists_lt_lower_semicontinuous_integral_gt_nnreal fp int_fp δpos with
    ⟨gp, fp_lt_gp, gpcont, gp_lt_top, gp_integrable, gpint⟩
  let fm : α → ℝ≥0 := fun x => Real.toNNReal (-f x)
  have int_fm : integrable (fun x => (fm x : ℝ)) μ := hf.neg.real_to_nnreal
  rcases exists_upper_semicontinuous_le_integral_le fm int_fm δpos with
    ⟨gm, gm_le_fm, gmcont, gm_integrable, gmint⟩
  let g : α → EReal := fun x => (gp x : EReal) - gm x
  have ae_g : ∀ᵐ x ∂μ, (g x).toReal = (gp x : EReal).toReal - (gm x : EReal).toReal :=
    by
    filter_upwards [gp_lt_top] with _ hx
    rw [EReal.toReal_sub] <;> simp [hx.ne]
  refine' ⟨g, _, _, _, _, _⟩
  show integrable (fun x => EReal.toReal (g x)) μ
  · rw [integrable_congr ae_g]
    convert gp_integrable.sub gm_integrable
    ext x
    simp
  show (∫ x : α, (g x).toReal ∂μ) < (∫ x : α, f x ∂μ) + ε;
  exact
    calc
      (∫ x : α, (g x).toReal ∂μ) = ∫ x : α, EReal.toReal (gp x) - EReal.toReal (gm x) ∂μ :=
        integral_congr_ae ae_g
      _ = (∫ x : α, EReal.toReal (gp x) ∂μ) - ∫ x : α, gm x ∂μ :=
        by
        simp only [EReal.toReal_coe_ennreal, ENNReal.coe_toReal, coe_coe]
        exact integral_sub gp_integrable gm_integrable
      _ < (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ∫ x : α, gm x ∂μ :=
        by
        apply sub_lt_sub_right
        convert gpint
        simp only [EReal.toReal_coe_ennreal]
      _ ≤ (∫ x : α, ↑(fp x) ∂μ) + ↑δ - ((∫ x : α, fm x ∂μ) - δ) := (sub_le_sub_left gmint _)
      _ = (∫ x : α, f x ∂μ) + 2 * δ := by
        simp_rw [integral_eq_integral_pos_part_sub_integral_neg_part hf, fp, fm]; ring
      _ = (∫ x : α, f x ∂μ) + ε := by congr 1; field_simp [δ, mul_comm]
      
  show ∀ᵐ x : α ∂μ, g x < ⊤
  · filter_upwards [gp_lt_top] with _ hx
    simp only [g, sub_eq_add_neg, coe_coe, Ne.def, (EReal.add_lt_top _ _).Ne, lt_top_iff_ne_top,
      lt_top_iff_ne_top.1 hx, EReal.coe_ennreal_eq_top_iff, not_false_iff, EReal.neg_eq_top_iff,
      EReal.coe_ennreal_ne_bot]
  show ∀ x, (f x : EReal) < g x
  · intro x
    rw [EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (f x)]
    refine' EReal.sub_lt_sub_of_lt_of_le _ _ _ _
    · simp only [EReal.coe_ennreal_lt_coe_ennreal_iff, coe_coe]; exact fp_lt_gp x
    · simp only [ENNReal.coe_le_coe, EReal.coe_ennreal_le_coe_ennreal_iff, coe_coe]
      exact gm_le_fm x
    · simp only [EReal.coe_ennreal_ne_bot, Ne.def, not_false_iff, coe_coe]
    · simp only [EReal.coe_nnreal_ne_top, Ne.def, not_false_iff, coe_coe]
  show LowerSemicontinuous g
  · apply LowerSemicontinuous.add'
    ·
      exact
        continuous_coe_ennreal_ereal.comp_lower_semicontinuous gpcont fun x y hxy =>
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy
    · apply
        ereal.continuous_neg.comp_upper_semicontinuous_antitone _ fun x y hxy =>
          EReal.neg_le_neg_iff.2 hxy
      dsimp
      apply
        continuous_coe_ennreal_ereal.comp_upper_semicontinuous _ fun x y hxy =>
          EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy
      exact
        ennreal.continuous_coe.comp_upper_semicontinuous gmcont fun x y hxy =>
          ENNReal.coe_le_coe.2 hxy
    · intro x
      exact EReal.continuousAt_add (by simp) (by simp)
#align measure_theory.exists_lt_lower_semicontinuous_integral_lt MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt

/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g < f` which is upper semicontinuous, with integral arbitrarily close to that
of `f`. This function has to be `ereal`-valued in general. -/
theorem exists_upperSemicontinuous_lt_integral_gt [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ)
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ g : α → EReal,
      (∀ x, (g x : EReal) < f x) ∧
        UpperSemicontinuous g ∧
          Integrable (fun x => EReal.toReal (g x)) μ ∧
            (∀ᵐ x ∂μ, ⊥ < g x) ∧ (∫ x, f x ∂μ) < (∫ x, EReal.toReal (g x) ∂μ) + ε :=
  by
  rcases exists_lt_lower_semicontinuous_integral_lt (fun x => -f x) hf.neg εpos with
    ⟨g, g_lt_f, gcont, g_integrable, g_lt_top, gint⟩
  refine' ⟨fun x => -g x, _, _, _, _, _⟩
  · exact fun x => EReal.neg_lt_iff_neg_lt.1 (by simpa only [EReal.coe_neg] using g_lt_f x)
  ·
    exact
      ereal.continuous_neg.comp_lower_semicontinuous_antitone gcont fun x y hxy =>
        EReal.neg_le_neg_iff.2 hxy
  · convert g_integrable.neg
    ext x
    simp
  · simpa [bot_lt_iff_ne_bot, lt_top_iff_ne_top] using g_lt_top
  · simp_rw [integral_neg, lt_neg_add_iff_add_lt] at gint 
    rw [add_comm] at gint 
    simpa [integral_neg] using gint
#align measure_theory.exists_upper_semicontinuous_lt_integral_gt MeasureTheory.exists_upperSemicontinuous_lt_integral_gt

end MeasureTheory


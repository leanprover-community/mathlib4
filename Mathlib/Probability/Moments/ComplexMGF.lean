/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Batteries.Tactic.Congr
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# The complex-valued moment-generating function

The moment-generating function (mgf) is `t : ℝ ↦ μ[fun ω ↦ rexp (t * X ω)]`. It can be extended to
a complex function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`, which we call `complexMGF X μ`.
That function is holomorphic on the vertical strip with base the interior of the interval
of definition of the mgf.
On the vertical line that goes through 0, `complexMGF X μ` is equal to the characteristic function.
This allows us to link properties of the characteristic function and the mgf (mostly deducing
properties of the mgf from those of the characteristic function).

## Main definitions

* `complexMGF X μ`: the function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`.

## Main results

* `complexMGF_ofReal`: for `x : ℝ`, `complexMGF X μ x = mgf X μ x`.

* `hasDerivAt_complexMGF`: for all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`.
* `differentiableOn_complexMGF`: `complexMGF X μ` is holomorphic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
* `analyticOn_complexMGF`: `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.

* `eqOn_complexMGF_of_mgf`: if two random variables have the same moment-generating function,
  then they have the same `complexMGF` on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
  Once we know that equal `mgf` implies equal distributions, we will be able to show that
  the `complexMGF` are equal everywhere, not only on the strip.
  This lemma will be used in the proof of the equality of distributions.

* `ext_of_complexMGF_eq`: If the complex moment-generating functions of two random variables `X`
  and `Y` with respect to the finite measures `μ`, `μ'`, respectively, coincide, then
  `μ.map X = μ'.map Y`. In other words, complex moment-generating functions separate the
  distributions of random variables.

## TODO

* Prove that if two random variables have the same `mgf`, then the have the same `complexMGF`.

-/

@[expose] public section


open MeasureTheory Filter Finset Real Complex

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ} {z ε : ℂ}

/-- Complex extension of the moment-generating function. -/
noncomputable
def complexMGF (X : Ω → ℝ) (μ : Measure Ω) (z : ℂ) : ℂ := ∫ ω, cexp (z * X ω) ∂μ

lemma complexMGF_undef (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω ↦ rexp (z.re * X ω)) μ) :
    complexMGF X μ z = 0 := by
  rw [complexMGF, integral_undef]
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [Complex.norm_exp] using h

lemma complexMGF_id_map (hX : AEMeasurable X μ) : complexMGF id (μ.map X) = complexMGF X μ := by
  ext t
  rw [complexMGF, integral_map hX]
  · rfl
  · fun_prop

lemma complexMGF_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (h : IdentDistrib X Y μ μ') :
    complexMGF X μ = complexMGF Y μ' := by
  rw [← complexMGF_id_map h.aemeasurable_fst, ← complexMGF_id_map h.aemeasurable_snd, h.map_eq]

lemma norm_complexMGF_le_mgf : ‖complexMGF X μ z‖ ≤ mgf X μ z.re := by
  rw [complexMGF, ← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ ≤ ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.norm_exp]

lemma complexMGF_ofReal (x : ℝ) : complexMGF X μ x = mgf X μ x := by
  rw [complexMGF, mgf]
  norm_cast

lemma re_complexMGF_ofReal (x : ℝ) : (complexMGF X μ x).re = mgf X μ x := by
  simp [complexMGF_ofReal]

lemma re_complexMGF_ofReal' : (fun x : ℝ ↦ (complexMGF X μ x).re) = mgf X μ := by
  ext x
  exact re_complexMGF_ofReal x

lemma complexMGF_id_mul_I {μ : Measure ℝ} (t : ℝ) :
    complexMGF id μ (t * I) = charFun μ t := by
  simp only [complexMGF, id_eq, charFun, RCLike.inner_apply, conj_trivial, ofReal_mul]
  congr with x
  ring_nf

lemma complexMGF_mul_I (hX : AEMeasurable X μ) (t : ℝ) :
    complexMGF X μ (t * I) = charFun (μ.map X) t := by
  rw [← complexMGF_id_map hX, complexMGF_id_mul_I]

section Analytic

/-- For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the derivative of the function
`z' ↦ μ[X ^ n * cexp (z' * X)]` at `z` is `μ[X ^ (n + 1) * cexp (z * X)]`. -/
lemma hasDerivAt_integral_pow_mul_exp (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun z ↦ μ[fun ω ↦ X ω ^ n * cexp (z * X ω)])
        μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  have hz' := hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω ↦ |X ω| ^ (n + 1) * rexp (z.re * X ω + t / 2 * |X ω|))
    (F := fun z ω ↦ X ω ^ n * cexp (z * X ω))
    (F' := fun z ω ↦ X ω ^ (n + 1) * cexp (z * X ω)) (Metric.ball_mem_nhds _ (half_pos ht))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z ↦ by fun_prop
  · exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz n
  · fun_prop
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this, add_re, add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    refine (abs_re_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · refine integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ ?_ ?_ (t := t) (n + 1)
    · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
    · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · positivity
    · exact lt_of_lt_of_le (by simp [ht]) (le_abs_self _)
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only
    simp_rw [pow_succ, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_ℂ]
    convert hasDerivAt_exp_smul_const (X ω : ℂ) ε using 1
    rw [smul_eq_mul, mul_comm]

/-- For all `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`,
`complexMGF X μ` is differentiable at `z` with derivative `μ[X * exp (z * X)]`. -/
theorem hasDerivAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (complexMGF X μ) μ[fun ω ↦ X ω * cexp (z * X ω)] z := by
  convert hasDerivAt_integral_pow_mul_exp hz 0
  · simp [complexMGF]
  · simp

/-- `complexMGF X μ` is holomorphic on the vertical strip
`{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
theorem differentiableOn_complexMGF :
    DifferentiableOn ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} := by
  intro z hz
  have h := hasDerivAt_complexMGF hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

theorem analyticOnNhd_complexMGF :
    AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
  differentiableOn_complexMGF.analyticOnNhd (isOpen_interior.preimage Complex.continuous_re)

/-- `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
theorem analyticOn_complexMGF :
    AnalyticOn ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
  analyticOnNhd_complexMGF.analyticOn

/-- `complexMGF X μ` is analytic at any point `z` with `z.re ∈ interior (integrableExpSet X μ)`. -/
lemma analyticAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℂ (complexMGF X μ) z :=
  analyticOnNhd_complexMGF z hz

end Analytic

section Deriv

/-! ### Iterated derivatives of `complexMGF` -/

lemma hasDerivAt_iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (iteratedDeriv n (complexMGF X μ)) μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  induction n generalizing z with
  | zero => simp [hasDerivAt_complexMGF hz]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (complexMGF X μ))
        =ᶠ[𝓝 z] fun z ↦ μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] := by
      have h_mem : ∀ᶠ y in 𝓝 z, y.re ∈ interior (integrableExpSet X μ) := by
        refine IsOpen.eventually_mem ?_ hz
        exact isOpen_interior.preimage Complex.continuous_re
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp hz (n + 1)

/-- For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the n-th derivative of the function
`complexMGF X μ` at `z` is `μ[X ^ n * cexp (z * X)]`. -/
lemma iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF X μ) z = μ[fun ω ↦ X ω ^ n * cexp (z * X ω)] := by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_complexMGF hz n).deriv

end Deriv

section EqOfMGF

/-! We prove that if two random variables have the same `mgf`, then
they also have the same `complexMGF`. -/

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' → ℝ} {μ' : Measure Ω'}

/-- If two random variables have the same moment-generating function then they have
the same `integrableExpSet`. -/
lemma integrableExpSet_eq_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq]
  by_cases hμ : μ = 0
  · simp [hμ, hμμ'.mp hμ]
  have : NeZero μ := ⟨hμ⟩
  have : NeZero μ' := ⟨(not_iff_not.mpr hμμ').mp hμ⟩
  rw [← mgf_pos_iff, ← mgf_pos_iff, hXY]

/-- If two random variables have the same moment-generating function then they have
the same `integrableExpSet`. -/
lemma integrableExpSet_eq_of_mgf [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  refine integrableExpSet_eq_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 ≠ 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

/-- If two random variables have the same moment-generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`.

TODO: once we know that equal `mgf` implies equal distributions, we will be able to show that
the `complexMGF` are equal everywhere, not only on the strip.
This lemma will be used in the proof of the equality of distributions. -/
lemma eqOn_complexMGF_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet X μ)} := by
  by_cases h_empty : interior (integrableExpSet X μ) = ∅
  · simp [h_empty]
  rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at h_empty
  obtain ⟨t, ht⟩ := h_empty
  have hX : AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd ℂ (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf' hXY hμμ'] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
    (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
    (z₀ := (t : ℂ)) (by simp [ht]) ?_
  have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] t, complexMGF X μ x = complexMGF Y μ' x := by
    refine .of_forall fun y ↦ ?_
    rw [complexMGF_ofReal, complexMGF_ofReal, hXY]
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

/-- If two random variables have the same moment-generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
lemma eqOn_complexMGF_of_mgf [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet X μ)} := by
  refine eqOn_complexMGF_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 ≠ 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

end EqOfMGF

section ext

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' → ℝ} {μ' : Measure Ω'}

/-- If the complex moment-generating functions of two random variables `X` and `Y` with respect to
the finite measures `μ`, `μ'`, respectively, coincide, then `μ.map X = μ'.map Y`. In other words,
complex moment-generating functions separate the distributions of random variables. -/
theorem _root_.MeasureTheory.Measure.ext_of_complexMGF_eq [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (h : complexMGF X μ = complexMGF Y μ') :
    μ.map X = μ'.map Y := by
  have inner_ne_zero (x : ℝ) (h : x ≠ 0) : innerₗ ℝ x ≠ 0 :=
    DFunLike.ne_iff.mpr ⟨x, inner_self_ne_zero.mpr h⟩
  apply MeasureTheory.ext_of_integral_char_eq continuous_probChar probChar_ne_one inner_ne_zero
    continuous_inner (fun w ↦ ?_)
  rw [funext_iff] at h
  specialize h (Multiplicative.toAdd w * I)
  simp_rw [complexMGF, mul_assoc, mul_comm I, ← mul_assoc] at h
  simp only [BoundedContinuousFunction.char_apply, innerₗ_apply_apply,
    RCLike.inner_apply, conj_trivial, probChar_apply, ofReal_mul]
  rwa [integral_map hX (by fun_prop), integral_map hY (by fun_prop)]

lemma _root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq
    {μ μ' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : complexMGF id μ = complexMGF id μ') :
    μ = μ' := by
  simpa using Measure.ext_of_complexMGF_eq aemeasurable_id aemeasurable_id h

end ext

end ProbabilityTheory

/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Patrick Massot, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.IndicatorFunction
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The dominated convergence theorem

This file collects various results related to the Lebesgue dominated convergence theorem
for the Bochner integral.

## Main results
- `MeasureTheory.tendsto_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for the Bochner integral
- `MeasureTheory.hasSum_integral_of_dominated_convergence`:
  the Lebesgue dominated convergence theorem for series
- `MeasureTheory.integral_tsum`, `MeasureTheory.integral_tsum_of_summable_integral_norm`:
  the integral and `tsum`s commute, if the norms of the functions form a summable series
- `intervalIntegral.hasSum_integral_of_dominated_convergence`: the Lebesgue dominated convergence
  theorem for parametric interval integrals
- `intervalIntegral.continuous_of_dominated_interval`: continuity of the interval integral
  w.r.t. a parameter
- `intervalIntegral.continuous_primitive` and friends: primitives of interval integrable
  measurable functions are continuous

-/

public section

open MeasureTheory Metric

/-!
## The Lebesgue dominated convergence theorem for the Bochner integral
-/
section DominatedConvergenceTheorem

open Set Filter TopologicalSpace ENNReal
open scoped Topology Interval

namespace MeasureTheory

variable {α E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m : MeasurableSpace α} {μ : Measure α}

/-- **Lebesgue dominated convergence theorem** provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals.
  We could weaken the condition `bound_integrable` to require `HasFiniteIntegral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → G} {f : α → G} (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
      bound F_measurable bound_integrable h_bound h_lim
  · simp [integral, hG]

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} {f : α → G} (bound : α → ℝ) (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 <| ∫ a, f a ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_filter_of_dominated_convergence (dominatedFinMeasAdditive_weightedSMul μ)
      bound hF_meas h_bound bound_integrable h_lim
  · simp [integral, hG, tendsto_const_nhds]

/-- Lebesgue dominated convergence theorem for series. -/
theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → α → G} {f : α → G}
    (bound : ι → α → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ, Summable fun n => bound n a)
    (bound_integrable : Integrable (fun a => ∑' n, bound n a) μ)
    (h_lim : ∀ᵐ a ∂μ, HasSum (fun n => F n a) (f a)) :
    HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ) := by
  have hb_nonneg : ∀ᵐ a ∂μ, ∀ n, 0 ≤ bound n a :=
    eventually_countable_forall.2 fun n => (h_bound n).mono fun a => (norm_nonneg _).trans
  have hb_le_tsum : ∀ n, bound n ≤ᵐ[μ] fun a => ∑' n, bound n a := by
    intro n
    filter_upwards [hb_nonneg, bound_summable]
      with _ ha0 ha_sum using ha_sum.le_tsum _ fun i _ => ha0 i
  have hF_integrable : ∀ n, Integrable (F n) μ := by
    refine fun n => bound_integrable.mono' (hF_meas n) ?_
    exact EventuallyLE.trans (h_bound n) (hb_le_tsum n)
  simp only [HasSum, ← integral_finset_sum _ fun n _ => hF_integrable n]
  refine tendsto_integral_filter_of_dominated_convergence
      (fun a => ∑' n, bound n a) ?_ ?_ bound_integrable h_lim
  · exact Eventually.of_forall fun s => s.aestronglyMeasurable_fun_sum fun n _ => hF_meas n
  · filter_upwards with s
    filter_upwards [eventually_countable_forall.2 h_bound, hb_nonneg, bound_summable]
      with a hFa ha0 has
    calc
      ‖∑ n ∈ s, F n a‖ ≤ ∑ n ∈ s, bound n a := norm_sum_le_of_le _ fun n _ => hFa n
      _ ≤ ∑' n, bound n a := has.sum_le_tsum _ (fun n _ => ha0 n)

theorem integral_tsum {ι} [Countable ι] {f : ι → α → G} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ ≠ ∞) :
    ∫ a : α, ∑' i, f i a ∂μ = ∑' i, ∫ a : α, f i a ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hf'' i : AEMeasurable (‖f i ·‖ₑ) μ := (hf i).enorm
  have hhh : ∀ᵐ a : α ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  convert (MeasureTheory.hasSum_integral_of_dominated_convergence (fun i a => ‖f i a‖₊) hf _ hhh
          ⟨_, _⟩ _).tsum_eq.symm
  · intro n
    filter_upwards with x
    rfl
  · simp_rw [← NNReal.coe_tsum]
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.coe_nnreal_real
    apply AEMeasurable.nnreal_tsum
    exact fun i => (hf i).nnnorm.aemeasurable
  · dsimp [HasFiniteIntegral]
    have : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    convert this using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hhh] with a ha
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ha)
  · filter_upwards [hhh] with x hx
    exact hx.of_norm.hasSum

lemma hasSum_integral_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    HasSum (∫ a, F · a ∂μ) (∫ a, (∑' i, F i a) ∂μ) := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, hasSum_zero]
  rw [integral_tsum (fun i ↦ (hF_int i).1)]
  · exact (hF_sum.of_norm_bounded fun i ↦ norm_integral_le_integral_norm _).hasSum
  have (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ‖∫ a, ‖F i a‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF_int i).norm, coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (F i a)))]
    simp only [coe_nnnorm]
  rw [funext this]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hF_sum.abs

lemma integral_tsum_of_summable_integral_norm {ι} [Countable ι] {F : ι → α → E}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    ∑' i, (∫ a, F i a ∂μ) = ∫ a, (∑' i, F i a) ∂μ :=
  (hasSum_integral_of_summable_integral_norm hF_int hF_sum).tsum_eq

/-- Corollary of the Lebesgue dominated convergence theorem: If a sequence of functions `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwise to a
function `f`, then the integrals of `F n` with respect to a finite measure `μ` converge
to the integral of `f`. -/
theorem tendsto_integral_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → G} [IsFiniteMeasure μ] {f : α → G}
    (h_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∃ C, ∀ᶠ n in l, (∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C))
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, F n ω ∂μ) l (nhds (∫ ω, f ω ∂μ)) := by
  obtain ⟨c, h_boundc⟩ := h_bound
  let C : α → ℝ := (fun _ => c)
  exact tendsto_integral_filter_of_dominated_convergence
    C h_meas h_boundc (integrable_const c) h_lim

end MeasureTheory

section TendstoMono

variable {α E : Type*} [MeasurableSpace α]
  {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℕ → Set α}
  {f : α → E}

theorem _root_.Antitone.tendsto_setIntegral (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : IntegrableOn f (s 0) μ) :
    Tendsto (fun i => ∫ a in s i, f a ∂μ) atTop (𝓝 (∫ a in ⋂ n, s n, f a ∂μ)) := by
  let bound : α → ℝ := indicator (s 0) fun a => ‖f a‖
  have h_int_eq : (fun i => ∫ a in s i, f a ∂μ) = fun i => ∫ a, (s i).indicator f a ∂μ :=
    funext fun i => (integral_indicator (hsm i)).symm
  rw [h_int_eq]
  rw [← integral_indicator (MeasurableSet.iInter hsm)]
  refine tendsto_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · intro n
    rw [aestronglyMeasurable_indicator_iff (hsm n)]
    exact (IntegrableOn.mono_set hfi (h_anti (zero_le n))).1
  · rw [integrable_indicator_iff (hsm 0)]
    exact hfi.norm
  · simp_rw [norm_indicator_eq_indicator_norm]
    refine fun n => Eventually.of_forall fun x => ?_
    grw [(h_anti (zero_le n)).subset]
  · filter_upwards [] with a using le_trans (h_anti.tendsto_indicator _ _ _) (pure_le_nhds _)

end TendstoMono

/-!
## The Lebesgue dominated convergence theorem for interval integrals
As an application, we show continuity of parametric integrals.
-/
namespace intervalIntegral

section DCT

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ}

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
nonrec theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → ℝ → E} (bound : ℝ → ℝ)
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ‖F n x‖ ≤ bound x)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_lim : ∀ᵐ x ∂μ, x ∈ Ι a b → Tendsto (fun n => F n x) l (𝓝 (f x))) :
    Tendsto (fun n => ∫ x in a..b, F n x ∂μ) l (𝓝 <| ∫ x in a..b, f x ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc,
    ← ae_restrict_iff' (α := ℝ) (μ := μ) measurableSet_uIoc] at *
  exact tendsto_const_nhds.smul <|
    tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim

/-- Lebesgue dominated convergence theorem for parametric interval integrals. -/
nonrec theorem hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι → ℝ → E}
    (bound : ι → ℝ → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) (μ.restrict (Ι a b)))
    (h_bound : ∀ n, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F n t‖ ≤ bound n t)
    (bound_summable : ∀ᵐ t ∂μ, t ∈ Ι a b → Summable fun n => bound n t)
    (bound_integrable : IntervalIntegrable (fun t => ∑' n, bound n t) μ a b)
    (h_lim : ∀ᵐ t ∂μ, t ∈ Ι a b → HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in a..b, F n t ∂μ) (∫ t in a..b, f t ∂μ) := by
  simp only [intervalIntegrable_iff, intervalIntegral_eq_integral_uIoc, ←
    ae_restrict_iff' (α := ℝ) (μ := μ) measurableSet_uIoc] at *
  exact
    (hasSum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable bound_integrable
          h_lim).const_smul
      _

/-- Interval integrals commute with countable sums, when the supremum norms are summable (a
special case of the dominated convergence theorem). -/
theorem hasSum_intervalIntegral_of_summable_norm [Countable ι] {f : ι → C(ℝ, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖) :
    HasSum (fun i : ι => ∫ x in a..b, f i x) (∫ x in a..b, ∑' i : ι, f i x) := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE, hasSum_zero]
  apply hasSum_integral_of_dominated_convergence
    (fun i (x : ℝ) => ‖(f i).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖)
    (fun i => (map_continuous <| f i).aestronglyMeasurable)
  · intro i; filter_upwards with x hx
    apply ContinuousMap.norm_coe_le_norm ((f i).restrict _) ⟨x, _⟩
    exact ⟨hx.1.le, hx.2⟩
  · exact ae_of_all _ fun x _ => hf_sum
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => Summable.hasSum ?_
    let x : (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ) := ⟨x, ⟨hx.1.le, hx.2⟩⟩
    have := hf_sum.of_norm
    simpa only [Compacts.coe_mk, ContinuousMap.restrict_apply]
      using ContinuousMap.summable_apply this x

theorem tsum_intervalIntegral_eq_of_summable_norm [Countable ι] {f : ι → C(ℝ, E)}
    (hf_sum : Summable fun i : ι => ‖(f i).restrict (⟨uIcc a b, isCompact_uIcc⟩ : Compacts ℝ)‖) :
    ∑' i : ι, ∫ x in a..b, f i x = ∫ x in a..b, ∑' i : ι, f i x :=
  (hasSum_intervalIntegral_of_summable_norm hf_sum).tsum_eq

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/-- Continuity of interval integral with respect to a parameter, at a point within a set.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀` within `s` and at `x₀`, and assume it is bounded by a function integrable
  on `[a, b]` independent of `x` in a neighborhood of `x₀` within `s`. If `(fun x ↦ F x t)`
  is continuous at `x₀` within `s` for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`. -/
theorem continuousWithinAt_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    {s : Set X} (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousWithinAt (fun x => F x t) s x₀) :
    ContinuousWithinAt (fun x => ∫ t in a..b, F x t ∂μ) s x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter at a point.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀`, and assume it is bounded by a function integrable on
  `[a, b]` independent of `x` in a neighborhood of `x₀`. If `(fun x ↦ F x t)`
  is continuous at `x₀` for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`. -/
theorem continuousAt_of_dominated_interval {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → ContinuousAt (fun x => F x t) x₀) :
    ContinuousAt (fun x => ∫ t in a..b, F x t ∂μ) x₀ :=
  tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter.
  Given `F : X → ℝ → E`, assume each `F x` is ae-measurable on `[a, b]`,
  and assume it is bounded by a function integrable on `[a, b]` independent of `x`.
  If `(fun x ↦ F x t)` is continuous for almost every `t` in `[a, b]`
  then the same holds for `(fun x ↦ ∫ t in a..b, F x t ∂μ) s x₀`. -/
theorem continuous_of_dominated_interval {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) <| μ.restrict <| Ι a b)
    (h_bound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → Continuous fun x => F x t) :
    Continuous fun x => ∫ t in a..b, F x t ∂μ :=
  continuous_iff_continuousAt.mpr fun _ =>
    continuousAt_of_dominated_interval (Eventually.of_forall hF_meas) (Eventually.of_forall h_bound)
        bound_integrable <|
      h_cont.mono fun _ himp hx => (himp hx).continuousAt

end DCT

section ContinuousPrimitive

open scoped Interval

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
  {a b b₀ b₁ b₂ : ℝ} {μ : Measure ℝ} {f : ℝ → E}

theorem continuousWithinAt_primitive (hb₀ : μ {b₀} = 0)
    (h_int : IntervalIntegrable f μ (min a b₁) (max a b₂)) :
    ContinuousWithinAt (fun b => ∫ x in a..b, f x ∂μ) (Icc b₁ b₂) b₀ := by
  by_cases h₀ : b₀ ∈ Icc b₁ b₂
  · have h₁₂ : b₁ ≤ b₂ := h₀.1.trans h₀.2
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂
    have h_int' : ∀ {x}, x ∈ Icc b₁ b₂ → IntervalIntegrable f μ b₁ x := by
      rintro x ⟨h₁, h₂⟩
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_right a b₁),
          h₁.trans (h₂.trans <| le_max_of_le_right <| le_max_right _ _)⟩
      · exact ⟨min_le_of_left_le <| (min_le_right _ _).trans h₁,
          le_max_of_le_right <| h₂.trans <| le_max_right _ _⟩
    have : ∀ b ∈ Icc b₁ b₂,
        ∫ x in a..b, f x ∂μ = (∫ x in a..b₁, f x ∂μ) + ∫ x in b₁..b, f x ∂μ := by
      rintro b ⟨h₁, h₂⟩
      rw [← integral_add_adjacent_intervals _ (h_int' ⟨h₁, h₂⟩)]
      apply h_int.mono_set
      apply uIcc_subset_uIcc
      · exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩
      · exact ⟨min_le_of_left_le (min_le_right _ _),
          le_max_of_le_right (h₁.trans <| h₂.trans (le_max_right a b₂))⟩
    apply ContinuousWithinAt.congr _ this (this _ h₀); clear this
    refine continuousWithinAt_const.add ?_
    have :
      (fun b => ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀] fun b =>
        ∫ x in b₁..b₂, indicator {x | x ≤ b} f x ∂μ := by
      apply eventuallyEq_of_mem self_mem_nhdsWithin
      exact fun b b_in => (integral_indicator b_in).symm
    apply ContinuousWithinAt.congr_of_eventuallyEq _ this (integral_indicator h₀).symm
    have : IntervalIntegrable (fun x => ‖f x‖) μ b₁ b₂ :=
      IntervalIntegrable.norm (h_int' <| right_mem_Icc.mpr h₁₂)
    refine continuousWithinAt_of_dominated_interval ?_ ?_ this ?_ <;> clear this
    · filter_upwards [self_mem_nhdsWithin]
      intro x hx
      rw [aestronglyMeasurable_indicator_iff, Measure.restrict_restrict, uIoc, Iic_def,
        Iic_inter_Ioc_of_le]
      · rw [min₁₂]
        exact (h_int' hx).1.aestronglyMeasurable
      · exact le_max_of_le_right hx.2
      exacts [measurableSet_Iic, measurableSet_Iic]
    · filter_upwards with x; filter_upwards with t
      dsimp [indicator]
      split_ifs <;> simp
    · have : ∀ᵐ t ∂μ, t < b₀ ∨ b₀ < t := by
        filter_upwards [compl_mem_ae_iff.mpr hb₀] with x hx using Ne.lt_or_gt hx
      apply this.mono
      rintro x₀ (hx₀ | hx₀) -
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = f x₀ := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Ioi_mem_nhds hx₀)
          intro x hx
          simp [hx.le]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀.le]
      · have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = 0 := by
          apply mem_nhdsWithin_of_mem_nhds
          apply Eventually.mono (Iio_mem_nhds hx₀)
          intro x hx
          simp [hx]
        apply continuousWithinAt_const.congr_of_eventuallyEq this
        simp [hx₀]
  · apply continuousWithinAt_of_notMem_closure
    rwa [closure_Icc]

theorem continuousAt_parametric_primitive_of_dominated [FirstCountableTopology X]
    {F : X → ℝ → E} (bound : ℝ → ℝ) (a b : ℝ)
    {a₀ b₀ : ℝ} {x₀ : X} (hF_meas : ∀ x, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ.restrict <| Ι a b, ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ.restrict <| Ι a b, ContinuousAt (fun x ↦ F x t) x₀) (ha₀ : a₀ ∈ Ioo a b)
    (hb₀ : b₀ ∈ Ioo a b) (hμb₀ : μ {b₀} = 0) :
    ContinuousAt (fun p : X × ℝ ↦ ∫ t : ℝ in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) := by
  have hsub : ∀ {a₀ b₀}, a₀ ∈ Ioo a b → b₀ ∈ Ioo a b → Ι a₀ b₀ ⊆ Ι a b := fun ha₀ hb₀ ↦
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b ∈ 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x₀ t‖ ≤ bound t := h_bound.self_of_nhds
  have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
    dsimp
    have hiF : ∀ {x a₀ b₀},
        (∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t) → a₀ ∈ Ioo a b → b₀ ∈ Ioo a b →
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ ↦
      (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub, add_assoc, add_sub_cancel,
      intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (Eventually.of_forall fun x ↦ (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx ↦
            ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
          (bound_integrable.mono_set_ae <| Eventually.of_forall <| hsub ha₀ hb₀) <|
          ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t ↦ ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices Tendsto (fun x : X × ℝ ↦ ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0) by
      simpa [ContinuousAt]
    have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ ≤ |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
      have H : ∀ᵐ t : ℝ ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ ≤ 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ ≤ ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ ≤ 2 * bound s := by linarith only [hs₁, hs₂]
      exact intervalIntegral.norm_integral_le_abs_of_norm_le H
        ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

variable [NoAtoms μ]

theorem continuousOn_primitive (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Ioc a x, f t ∂μ) (Icc a b) := by
  by_cases h : a ≤ b
  · have : ∀ x ∈ Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫ t in a..x, f t ∂μ := by
      intro x x_in
      simp_rw [integral_of_le x_in.1]
    rw [continuousOn_congr this]
    intro x₀ _
    refine continuousWithinAt_primitive (measure_singleton x₀) ?_
    simp only [intervalIntegrable_iff_integrableOn_Ioc_of_le, max_eq_right, h, min_self]
    exact h_int.mono Ioc_subset_Icc_self le_rfl
  · rw [Icc_eq_empty h]
    exact continuousOn_empty _

theorem continuousOn_primitive_Icc (h_int : IntegrableOn f (Icc a b) μ) :
    ContinuousOn (fun x => ∫ t in Icc a x, f t ∂μ) (Icc a b) := by
  have aux : (fun x => ∫ t in Icc a x, f t ∂μ) = fun x => ∫ t in Ioc a x, f t ∂μ := by
    ext x
    exact integral_Icc_eq_integral_Ioc
  rw [aux]
  exact continuousOn_primitive h_int

/-- Note: this assumes that `f` is `IntervalIntegrable`, in contrast to some other lemmas here. -/
theorem continuousOn_primitive_interval' (h_int : IntervalIntegrable f μ b₁ b₂)
    (ha : a ∈ [[b₁, b₂]]) : ContinuousOn (fun b => ∫ x in a..b, f x ∂μ) [[b₁, b₂]] := fun _ _ ↦ by
  refine continuousWithinAt_primitive (measure_singleton _) ?_
  rw [min_eq_right ha.1, max_eq_right ha.2]
  simpa [intervalIntegrable_iff, uIoc] using h_int

theorem continuousOn_primitive_interval (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in a..x, f t ∂μ) (uIcc a b) :=
  continuousOn_primitive_interval' h_int.intervalIntegrable left_mem_uIcc

theorem continuousOn_primitive_interval_left (h_int : IntegrableOn f (uIcc a b) μ) :
    ContinuousOn (fun x => ∫ t in x..b, f t ∂μ) (uIcc a b) := by
  rw [uIcc_comm a b] at h_int ⊢
  simp only [integral_symm b]
  exact (continuousOn_primitive_interval h_int).neg

theorem continuous_primitive (h_int : ∀ a b, IntervalIntegrable f μ a b) (a : ℝ) :
    Continuous fun b => ∫ x in a..b, f x ∂μ := by
  rw [continuous_iff_continuousAt]
  intro b₀
  obtain ⟨b₁, hb₁⟩ := exists_lt b₀
  obtain ⟨b₂, hb₂⟩ := exists_gt b₀
  apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₁ hb₂)
  exact continuousWithinAt_primitive (measure_singleton b₀) (h_int _ _)

nonrec theorem _root_.MeasureTheory.Integrable.continuous_primitive (h_int : Integrable f μ)
    (a : ℝ) : Continuous fun b => ∫ x in a..b, f x ∂μ :=
  continuous_primitive (fun _ _ => h_int.intervalIntegrable) a

variable [IsLocallyFiniteMeasure μ] {f : X → ℝ → E}

theorem continuous_parametric_primitive_of_continuous
    {a₀ : ℝ} (hf : Continuous f.uncurry) :
    Continuous fun p : X × ℝ ↦ ∫ t in a₀..p.2, f p.1 t ∂μ := by
  -- We will prove continuity at a point `(q, b₀)`.
  rw [continuous_iff_continuousAt]
  rintro ⟨q, b₀⟩
  apply Metric.continuousAt_iff'.2 (fun ε εpos ↦ ?_)
  -- choose `a` and `b` such that `(a, b)` contains both `a₀` and `b₀`. We will use uniform
  -- estimates on a neighborhood of the compact set `{q} × [a, b]`.
  obtain ⟨a, a_lt⟩ := exists_lt (min a₀ b₀)
  obtain ⟨b, lt_b⟩ := exists_gt (max a₀ b₀)
  rw [lt_min_iff] at a_lt
  rw [max_lt_iff] at lt_b
  have : IsCompact ({q} ×ˢ (Icc a b)) := isCompact_singleton.prod isCompact_Icc
  -- let `M` be a bound for `f` on the compact set `{q} × [a, b]`.
  obtain ⟨M, hM⟩ := this.bddAbove_image hf.norm.continuousOn
  -- let `δ` be small enough to satisfy several properties that will show up later.
  obtain ⟨δ, δpos, hδ, h'δ, h''δ⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 1 ∧ Icc (b₀ - δ) (b₀ + δ) ⊆ Icc a b ∧
      (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
    have A : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    have B : ∀ᶠ δ in 𝓝 0, Icc (b₀ - δ) (b₀ + δ) ⊆ Icc a b := by
      have I : Tendsto (fun δ ↦ b₀ - δ) (𝓝 0) (𝓝 (b₀ - 0)) := tendsto_const_nhds.sub tendsto_id
      have J : Tendsto (fun δ ↦ b₀ + δ) (𝓝 0) (𝓝 (b₀ + 0)) := tendsto_const_nhds.add tendsto_id
      simp only [sub_zero, add_zero] at I J
      filter_upwards [(tendsto_order.1 I).1 _ a_lt.2, (tendsto_order.1 J).2 _ lt_b.2] with δ hδ h'δ
      exact Icc_subset_Icc hδ.le h'δ.le
    have C : ∀ᶠ δ in 𝓝 0,
        (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) < ε := by
      suffices Tendsto
        (fun δ ↦ (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b))
          (𝓝 0) (𝓝 ((M + 1) * (0 : ℝ≥0∞).toReal + 0 * μ.real (Icc a b))) by
        simp only [toReal_zero, mul_zero, zero_mul, add_zero] at this
        exact (tendsto_order.1 this).2 _ εpos
      apply Tendsto.add (Tendsto.mul tendsto_const_nhds _)
        (Tendsto.mul tendsto_id tendsto_const_nhds)
      exact (tendsto_toReal zero_ne_top).comp (tendsto_measure_Icc _ _)
    rcases (A.and ((B.and C).filter_mono nhdsWithin_le_nhds)).exists with ⟨δ, hδ, h'δ, h''δ⟩
    exact ⟨δ, hδ.1, hδ.2, h'δ, h''δ⟩
  -- By compactness of `[a, b]` and continuity of `f` there, if `p` is close enough to `q`
  -- then `f p x` is `δ`-close to `f q x`, uniformly in `x ∈ [a, b]`.
  -- (Note in particular that this implies a bound `M + δ ≤ M + 1` for `f p x`).
  obtain ⟨v, v_mem, hv⟩ : ∃ v ∈ 𝓝[univ] q, ∀ p ∈ v, ∀ x ∈ Icc a b, dist (f p x) (f q x) < δ :=
    IsCompact.mem_uniformity_of_prod isCompact_Icc hf.continuousOn (mem_univ _)
      (dist_mem_uniformity δpos)
  -- for `p` in this neighborhood and `s` which is `δ`-close to `b₀`, we will show that the
  -- integrals are `ε`-close.
  have : v ×ˢ (Ioo (b₀ - δ) (b₀ + δ)) ∈ 𝓝 (q, b₀) := by
    rw [nhdsWithin_univ] at v_mem
    simp only [prod_mem_nhds_iff, v_mem, true_and]
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [this]
  rintro ⟨p, s⟩ ⟨hp : p ∈ v, hs : s ∈ Ioo (b₀ - δ) (b₀ + δ)⟩
  simp only [dist_eq_norm] at hv ⊢
  have J r u v : IntervalIntegrable (f r) μ u v := (hf.uncurry_left _).intervalIntegrable _ _
  /- we compute the difference between the integrals by splitting the contribution of the change
  from `b₀` to `s` (which gives a contribution controlled by the measure of `(b₀ - δ, b₀ + δ)`,
  small enough thanks to our choice of `δ`) and the change from `q` to `p`, which is small as
  `f p x` and `f q x` are uniformly close by design. -/
  calc
  ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖
    = ‖(∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ)
        + (∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ)‖ := by congr 1; abel
  _ ≤ ‖∫ t in a₀..s, f p t ∂μ - ∫ t in a₀..b₀, f p t ∂μ‖
        + ‖∫ t in a₀..b₀, f p t ∂μ - ∫ t in a₀..b₀, f q t ∂μ‖ := norm_add_le _ _
  _ = ‖∫ t in b₀..s, f p t ∂μ‖ + ‖∫ t in a₀..b₀, (f p t - f q t) ∂μ‖ := by
      congr 2
      · rw [integral_interval_sub_left (J _ _ _) (J _ _ _)]
      · rw [integral_sub (J _ _ _) (J _ _ _)]
  _ ≤ ∫ t in Ι b₀ s, ‖f p t‖ ∂μ + ∫ t in Ι a₀ b₀, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact norm_integral_le_integral_norm_uIoc
      · exact norm_integral_le_integral_norm_uIoc
  _ ≤ ∫ t in Icc (b₀ - δ) (b₀ + δ), ‖f p t‖ ∂μ + ∫ t in Icc a b, ‖f p t - f q t‖ ∂μ := by
      gcongr
      · exact Eventually.of_forall (fun x ↦ norm_nonneg _)
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · apply uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ⟨hs.1.le, hs.2.le⟩ )
        simp [δpos.le]
      · exact Eventually.of_forall (fun x ↦ norm_nonneg _)
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact uIoc_subset_uIcc.trans (uIcc_subset_Icc ⟨a_lt.1.le, lt_b.1.le⟩ ⟨a_lt.2.le, lt_b.2.le⟩)
  _ ≤ ∫ t in Icc (b₀ - δ) (b₀ + δ), M + 1 ∂μ + ∫ _t in Icc a b, δ ∂μ := by
      gcongr with x hx x hx
      · exact (hf.uncurry_left _).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · calc ‖f p x‖ = ‖f q x + (f p x - f q x)‖ := by congr; abel
        _ ≤ ‖f q x‖ + ‖f p x - f q x‖ := norm_add_le _ _
        _ ≤ M + δ := by
            gcongr
            · apply hM
              change (fun x ↦ ‖Function.uncurry f x‖) (q, x) ∈ _
              apply mem_image_of_mem
              simp only [singleton_prod, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
              exact h'δ hx
            · exact le_of_lt (hv _ hp _ (h'δ hx))
        _ ≤ M + 1 := by linarith
      · exact ((hf.uncurry_left _).sub (hf.uncurry_left _)).norm.integrableOn_Icc
      · exact continuous_const.integrableOn_Icc
      · exact nullMeasurableSet_Icc
      · exact le_of_lt (hv _ hp _ hx)
  _ = (M + 1) * μ.real (Icc (b₀ - δ) (b₀ + δ)) + δ * μ.real (Icc a b) := by simp [mul_comm]
  _ < ε := h''δ

@[fun_prop]
theorem continuous_parametric_intervalIntegral_of_continuous {a₀ : ℝ}
    (hf : Continuous f.uncurry) {s : X → ℝ} (hs : Continuous s) :
    Continuous fun x ↦ ∫ t in a₀..s x, f x t ∂μ :=
  show Continuous ((fun p : X × ℝ ↦ ∫ t in a₀..p.2, f p.1 t ∂μ) ∘ fun x ↦ (x, s x)) from
    (continuous_parametric_primitive_of_continuous hf).comp₂ continuous_id hs

theorem continuous_parametric_intervalIntegral_of_continuous'
    (hf : Continuous f.uncurry) (a₀ b₀ : ℝ) :
    Continuous fun x ↦ ∫ t in a₀..b₀, f x t ∂μ := by fun_prop

end ContinuousPrimitive

end intervalIntegral

namespace MeasureTheory

namespace IntegrableOn

open intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E}

theorem continuousWithinAt_Ici_primitive_Ioi {a₀ : ℝ} (hf : IntegrableOn f (Ioi a₀) μ) :
    ContinuousWithinAt (fun b ↦ ∫ x in Ioi b, f x ∂μ) (Ici a₀) a₀ := by
  simp_rw [← integral_indicator measurableSet_Ioi]
  apply tendsto_integral_filter_of_dominated_convergence ((Ioi a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioi]
    exact (hf.mono_set (Ioi_subset_Ioi ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x ↦ ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Ioi_subset_Ioi (by grind)) (fun a ↦ norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Ioi] using hf.norm
  · refine ae_of_all _ fun x ↦ ?_
    simp only [indicator_apply, mem_Ioi]
    by_cases hx : a₀ < x <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

theorem continuousOn_Ici_primitive_Ioi [NoAtoms μ] {a₀ : ℝ} (hf : IntegrableOn f (Ioi a₀) μ) :
    ContinuousOn (fun b ↦ ∫ x in Ioi b, f x ∂μ) (Ici a₀) := by
  intro a (ha : a₀ ≤ a)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · rw [Ici_inter_Iic]
    have h_int : IntervalIntegrable f μ a₀ a :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).2 <| hf.mono_set Ioc_subset_Ioi_self
    have h_split : ∀ b ∈ Icc a₀ a, ∫ x in Ioi b, f x ∂μ =
        (∫ x in Ioi a₀, f x ∂μ) - ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [← integral_Ioi_sub_Ioi hf hb.1]
    have h_cwa : ContinuousWithinAt (fun b ↦ ∫ x in a₀..b, f x ∂μ) (Icc a₀ a) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.sub h_cwa).congr h_split (h_split a (right_mem_Icc.2 ha))
  · simpa [ha] using (hf.mono_set (Ioi_subset_Ioi ha)).continuousWithinAt_Ici_primitive_Ioi

theorem continuousWithinAt_Iic_primitive_Iio {a₀ : ℝ} (hf : IntegrableOn f (Iio a₀) μ) :
    ContinuousWithinAt (fun b ↦ ∫ x in Iio b, f x ∂μ) (Iic a₀) a₀ := by
  simp_rw [← integral_indicator measurableSet_Iio]
  apply tendsto_integral_filter_of_dominated_convergence ((Iio a₀).indicator (norm ∘ f))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    rw [aestronglyMeasurable_indicator_iff measurableSet_Iio]
    exact (hf.mono_set (Iio_subset_Iio ha)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with a ha
    refine ae_of_all _ fun x ↦ ?_
    rw [norm_indicator_eq_indicator_norm]
    apply indicator_le_indicator_of_subset (Iio_subset_Iio (by grind)) (fun a ↦ norm_nonneg (f a))
  · simpa [integrable_indicator_iff measurableSet_Iio] using hf.norm
  · refine ae_of_all _ fun x ↦ ?_
    simp only [indicator_apply, mem_Iio]
    by_cases hx : x < a₀ <;> apply tendsto_const_nhds.congr'
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hx)] with a ha using by grind
    · filter_upwards [self_mem_nhdsWithin] with a ha using by grind

theorem continuousOn_Iic_primitive_Iio [NoAtoms μ] {a₀ : ℝ} (hf : IntegrableOn f (Iio a₀) μ) :
    ContinuousOn (fun b ↦ ∫ x in Iio b, f x ∂μ) (Iic a₀) := by
  intro a (ha : a ≤ a₀)
  rw [continuousWithinAt_iff_continuous_left_right]
  constructor
  · simpa [ha] using (hf.mono_set (Iio_subset_Iio ha)).continuousWithinAt_Iic_primitive_Iio
  · rw [Iic_inter_Ici]
    have h_int : IntervalIntegrable f μ a a₀ :=
      (intervalIntegrable_iff_integrableOn_Ico_of_le ha).2 <| hf.mono_set Ico_subset_Iio_self
    have h_split : ∀ b ∈ Icc a a₀, ∫ x in Iio b, f x ∂μ =
        (∫ x in Iio a₀, f x ∂μ) + ∫ x in a₀..b, f x ∂μ := by
      intro b hb
      simp [integral_symm b a₀, ← integral_Iio_sub_Iio' hf (hf.mono_set (Iio_subset_Iio hb.2))]
    have h_cwa : ContinuousWithinAt (fun b ↦ ∫ x in a₀..b, f x ∂μ) (Icc a a₀) a :=
      continuousWithinAt_primitive (measure_singleton a) (by simpa [ha])
    exact (continuousWithinAt_const.add h_cwa).congr h_split (h_split a (left_mem_Icc.2 ha))

theorem continuousOn_Ici_primitive_Ici [NoAtoms μ] {a₀ : ℝ} (hf : IntegrableOn f (Ici a₀) μ) :
    ContinuousOn (fun b ↦ ∫ x in Ici b, f x ∂μ) (Ici a₀) := by
  simp_rw [integral_Ici_eq_integral_Ioi]
  exact (hf.mono_set Ioi_subset_Ici_self).continuousOn_Ici_primitive_Ioi

theorem continuousOn_Iic_primitive_Iic [NoAtoms μ] {a₀ : ℝ} (hf : IntegrableOn f (Iic a₀) μ) :
    ContinuousOn (fun b ↦ ∫ x in Iic b, f x ∂μ) (Iic a₀) := by
  simp_rw [integral_Iic_eq_integral_Iio]
  exact (hf.mono_set Iio_subset_Iic_self).continuousOn_Iic_primitive_Iio

end IntegrableOn

end MeasureTheory

end DominatedConvergenceTheorem

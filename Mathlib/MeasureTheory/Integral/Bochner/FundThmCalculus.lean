/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.Tendsto
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
import Mathlib.Tactic.SetLike
import Mathlib.Topology.NhdsWithin

/-!
# Fundamental theorem of calculus for set integrals

This file proves a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integrals. See `Filter.Tendsto.integral_sub_linear_isLittleO_ae` and its corollaries.

Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ ae μ`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.smallSets`, i.e. for any `ε>0` there exists `t ∈ l` such that
`‖∫ x in s, f x ∂μ - μ s • c‖ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.
-/

public section

open Filter MeasureTheory Topology Asymptotics Metric

variable {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Fundamental theorem of calculus for set integrals:
if `μ` is a measure that is finite at a filter `l` and
`f` is a measurable function that has a finite limit `b` at `l ⊓ ae μ`, then
`∫ x in s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that
`s i` tends to `l.smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
theorem Filter.Tendsto.integral_sub_linear_isLittleO_ae
    {μ : Measure X} {l : Filter X} [l.IsMeasurablyGenerated] {f : X → E} {b : E}
    (h : Tendsto f (l ⊓ ae μ) (𝓝 b)) (hfm : StronglyMeasurableAtFilter f l μ)
    (hμ : μ.FiniteAtFilter l) {s : ι → Set X} {li : Filter ι} (hs : Tendsto s li l.smallSets)
    (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • b) =o[li] m := by
  suffices
      (fun s => (∫ x in s, f x ∂μ) - μ.real s • b) =o[l.smallSets] fun s => μ.real s from
    (this.comp_tendsto hs).congr'
      (hsμ.mono fun a ha => by dsimp only [Function.comp_apply] at ha ⊢; rw [ha]) hsμ
  refine isLittleO_iff.2 fun ε ε₀ => ?_
  have : ∀ᶠ s in l.smallSets, ∀ᵐ x ∂μ, x ∈ s → f x ∈ closedBall b ε :=
    eventually_smallSets_eventually.2 (h.eventually <| closedBall_mem_nhds _ ε₀)
  filter_upwards [hμ.eventually, (hμ.integrableAtFilter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this]
  simp only [mem_closedBall, dist_eq_norm]
  intro s hμs h_integrable hfm h_norm
  rw [← setIntegral_const,
    ← integral_sub h_integrable (integrableOn_const hμs.ne),
    Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact norm_setIntegral_le_of_norm_le_const_ae' hμs h_norm

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
theorem ContinuousWithinAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X}
    [IsLocallyFiniteMeasure μ] {x : X} {t : Set X} {f : X → E} (hx : ContinuousWithinAt f t x)
    (ht : MeasurableSet t) (hfm : StronglyMeasurableAtFilter f (𝓝[t] x) μ) {s : ι → Set X}
    {li : Filter ι} (hs : Tendsto s li (𝓝[t] x).smallSets) (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  haveI : (𝓝[t] x).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hx.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhdsWithin x t) hs m
    hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to
`(𝓝 a).smallSets` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in
the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
theorem ContinuousAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X}
    {f : X → E} (hx : ContinuousAt f x) (hfm : StronglyMeasurableAtFilter f (𝓝 x) μ) {s : ι → Set X}
    {li : Filter ι} (hs : Tendsto s li (𝓝 x).smallSets) (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  (hx.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhds x) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
theorem ContinuousOn.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X E] {μ : Measure X}
    [IsLocallyFiniteMeasure μ] {x : X} {t : Set X} {f : X → E} (hft : ContinuousOn f t) (hx : x ∈ t)
    (ht : MeasurableSet t) {s : ι → Set X} {li : Filter ι} (hs : Tendsto s li (𝓝[t] x).smallSets)
    (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  (hft x hx).integral_sub_linear_isLittleO_ae ht
    ⟨t, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩ hs m hsμ

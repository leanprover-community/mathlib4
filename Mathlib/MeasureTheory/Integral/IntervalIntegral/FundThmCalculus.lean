/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Fundamental Theorem of Calculus

We prove various versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for interval integrals in `ℝ`.

Recall that its first version states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫ x in a..b, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `intervalIntegral` namespace. Many of them follow
the naming scheme `integral_has(Strict?)(F?)Deriv(Within?)At(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `Has(Strict?)(F?)Deriv(Within?)At`.
Let us explain the meaning of each part of the name:

* `Strict` means that the theorem is about strict differentiability, see `HasStrictDerivAt` and
  `HasStrictFDerivAt`;
* `F` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `Within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(Within?)`. These theorems are named
`(f?)deriv(Within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae` states that
`(u, v) ↦ ∫ x in u..v, f x` has a derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t`
at `(a, b)` provided that `f` tends to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where
possible values of `s`, `t`, and corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `intervalIntegral.FTCFilter` to make Lean automatically find `la`/`lb` based on
`s`/`t`. This way we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial
ones not covered by `integral_hasDerivWithinAt_of_tendsto_ae_(left|right)` and
`integral_hasFDerivAt_of_tendsto_ae`). Similarly, `integral_hasDerivWithinAt_of_tendsto_ae_right`
works for both one-sided derivatives using the same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae`, states the following.
Let `(la, la')` be an `intervalIntegral.FTCFilter` pair of filters around `a` (i.e.,
`intervalIntegral.FTCFilter a la la'`) and let `(lb, lb')` be an `intervalIntegral.FTCFilter` pair
of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at `la'` and `lb'`,
respectively, then
$$
  \int_{va}^{vb} f ∂μ - \int_{ua}^{ub} f ∂μ =
  \int_{ub}^{vb} cb ∂μ - \int_{ua}^{va} ca ∂μ + o(‖∫_{ua}^{va} 1 ∂μ‖ + ‖∫_{ub}^{vb} (1:ℝ) ∂μ‖)
$$
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` - most general version, for functions
  with a right derivative
* `intervalIntegral.integral_eq_sub_of_hasDerivAt` - version for functions with a derivative on
  an open set
* `intervalIntegral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

Many applications of these theorems can be found in the directory
`Mathlib/Analysis/SpecialFunctions/Integrals/`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`ContinuousOn.intervalIntegrable` or `ContinuousOn.integrableOn_Icc` or
`ContinuousOn.integrableOn_uIcc`.

Versions of FTC-2 under the simpler assumption that the function is `C^1` are given in the
file `Mathlib/MeasureTheory/Integral/IntervalIntegral/ContDiff.lean`.

Applications to integration by parts are in the file
`Mathlib.MeasureTheory.Integral.IntegrationByParts`.

### `intervalIntegral.FTCFilter` class

As explained above, many theorems in this file rely on the typeclass
`intervalIntegral.FTCFilter (a : ℝ) (l l' : Filter ℝ)` to avoid code duplication. This typeclass
combines four assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `intervalIntegral.FTCFilter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Set.Icc a b] x, 𝓝[Set.Icc a b] x)` (resp.
`(x, 𝓝[Set.uIcc a b] x, 𝓝[Set.uIcc a b] x)`), with `x ∈ Icc a b` (resp. `x ∈ uIcc a b`). This
results in a two-sided derivatives for `x ∈ Set.Ioo a b` and one-sided derivatives for `x ∈ {a, b}`.
Other instances could be added when needed (in that case, one also needs to add instances for
`Filter.IsMeasurablyGenerated` and `Filter.TendstoIxxClass`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2
-/

public section

assert_not_exists HasDerivAt.mul -- guard against import creep

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace intervalIntegral

section FTC1

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`intervalIntegral.FTCFilter a l l'`. This typeclass has exactly four “real” instances:
`(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` can be
seen as a generalization of lemma `integral_hasStrictFDerivAt` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right-hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`. -/
class FTCFilter (a : outParam ℝ) (outer : Filter ℝ) (inner : outParam <| Filter ℝ) : Prop
    extends TendstoIxxClass Ioc outer inner where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ 𝓝 a
  [meas_gen : IsMeasurablyGenerated inner]

namespace FTCFilter


instance pure (a : ℝ) : FTCFilter a (pure a) ⊥ where
  pure_le := le_rfl
  le_nhds := bot_le

instance nhdsWithinSingleton (a : ℝ) : FTCFilter a (𝓝[{a}] a) ⊥ := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]; infer_instance

theorem finiteAt_inner {a : ℝ} (l : Filter ℝ) {l'} [h : FTCFilter a l l'] {μ : Measure ℝ}
    [IsLocallyFiniteMeasure μ] : μ.FiniteAtFilter l' :=
  (μ.finiteAt_nhds a).filter_mono h.le_nhds

instance nhds (a : ℝ) : FTCFilter a (𝓝 a) (𝓝 a) where
  pure_le := pure_le_nhds a
  le_nhds := le_rfl

instance nhdsUniv (a : ℝ) : FTCFilter a (𝓝[univ] a) (𝓝 a) := by rw [nhdsWithin_univ]; infer_instance

instance nhdsLeft (a : ℝ) : FTCFilter a (𝓝[≤] a) (𝓝[≤] a) where
  pure_le := pure_le_nhdsWithin self_mem_Iic
  le_nhds := inf_le_left

instance nhdsRight (a : ℝ) : FTCFilter a (𝓝[≥] a) (𝓝[>] a) where
  pure_le := pure_le_nhdsWithin self_mem_Ici
  le_nhds := inf_le_left

instance nhdsIcc {x a b : ℝ} [h : Fact (x ∈ Icc a b)] :
    FTCFilter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) where
  pure_le := pure_le_nhdsWithin h.out
  le_nhds := inf_le_left

instance nhdsUIcc {x a b : ℝ} [h : Fact (x ∈ [[a, b]])] :
    FTCFilter x (𝓝[[[a, b]]] x) (𝓝[[[a, b]]] x) :=
  .nhdsIcc (h := h)

end FTCFilter

section

variable {f : ℝ → E} {a b : ℝ} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι}
  {μ : Measure ℝ} {u v ua va ub vb : ι → ℝ}

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l' ⊓ ae μ`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.  The primed version
also works, e.g., for `l = l' = atTop`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  have A := hf.integral_sub_linear_isLittleO_ae hfm hl (hu.Ioc hv)
  have B := hf.integral_sub_linear_isLittleO_ae hfm hl (hv.Ioc hu)
  simp_rw [integral_const', sub_smul]
  refine ((A.trans_le fun t ↦ ?_).sub (B.trans_le fun t ↦ ?_)).congr_left fun t ↦ ?_
  · cases le_total (u t) (v t) <;> simp [*]
  · cases le_total (u t) (v t) <;> simp [*]
  · simp_rw [intervalIntegral]
    abel

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.  The primed version
also works, e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t =>
      μ.real (Ioc (u t) (v t)) :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf hl hu hv).congr'
    (huv.mono fun x hx => by simp [integral_const', hx])
    (huv.mono fun x hx => by simp [integral_const', hx])

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version. The primed version
also works, e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t =>
      μ.real (Ioc (v t) (u t)) :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf hl hv hu
          huv).neg_left.congr_left
    fun t => by simp [integral_symm (u t), add_comm]

section IsLocallyFiniteMeasure

variable [IsLocallyFiniteMeasure μ]

variable [FTCFilter a la la'] [FTCFilter b lb lb']

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae'` for a version that also works, e.g.,
for `l = l' = Filter.atTop`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf (FTCFilter.finiteAt_inner l) hu hv

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t =>
      μ.real (Ioc (u t) (v t)) :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = -μ (Set.Ioc v u) • c + o(μ(Set.Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = Filter.atTop`. -/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t =>
      μ.real (Ioc (v t) (u t)) :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

/-- **Fundamental theorem of calculus-1**, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f la' μ)
    (hmeas_b : StronglyMeasurableAtFilter f lb' μ) (ha_lim : Tendsto f (la' ⊓ ae μ) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae μ) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x ∂μ) - ∫ x in ua t..ub t, f x ∂μ) -
          ((∫ _ in ub t..vb t, cb ∂μ) - ∫ _ in ua t..va t, ca ∂μ)) =o[lt]
      fun t => ‖∫ _ in ua t..va t, (1 : ℝ) ∂μ‖ + ‖∫ _ in ub t..vb t, (1 : ℝ) ∂μ‖ := by
  haveI := FTCFilter.meas_gen la; haveI := FTCFilter.meas_gen lb
  refine
    ((measure_integral_sub_linear_isLittleO_of_tendsto_ae hmeas_a ha_lim hua hva).neg_left.add_add
          (measure_integral_sub_linear_isLittleO_of_tendsto_ae hmeas_b hb_lim hub hvb)).congr'
      ?_ EventuallyEq.rfl
  have A : ∀ᶠ t in lt, IntervalIntegrable f μ (ua t) (va t) :=
    ha_lim.eventually_intervalIntegrable_ae hmeas_a (FTCFilter.finiteAt_inner la) hua hva
  have A' : ∀ᶠ t in lt, IntervalIntegrable f μ a (ua t) :=
    ha_lim.eventually_intervalIntegrable_ae hmeas_a (FTCFilter.finiteAt_inner la)
      (tendsto_const_pure.mono_right FTCFilter.pure_le) hua
  have B : ∀ᶠ t in lt, IntervalIntegrable f μ (ub t) (vb t) :=
    hb_lim.eventually_intervalIntegrable_ae hmeas_b (FTCFilter.finiteAt_inner lb) hub hvb
  have B' : ∀ᶠ t in lt, IntervalIntegrable f μ b (ub t) :=
    hb_lim.eventually_intervalIntegrable_ae hmeas_b (FTCFilter.finiteAt_inner lb)
      (tendsto_const_pure.mono_right FTCFilter.pure_le) hub
  filter_upwards [A, A', B, B'] with _ ua_va a_ua ub_vb b_ub
  rw [← integral_interval_sub_interval_comm']
  · abel
  exacts [ub_vb, ua_va, b_ub.symm.trans <| hab.symm.trans a_ua]

/-- **Fundamental theorem of calculus-1**, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of
`intervalIntegral.FTCFilter`s around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ ae μ`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)` as
`u` and `v` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f lb' μ)
    (hf : Tendsto f (lb' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x ∂μ) - ∫ x in a..u t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  simpa using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab stronglyMeasurableAt_bot
      hmeas ((tendsto_bot : Tendsto _ ⊥ (𝓝 (0 : E))).mono_left inf_le_left) hf
      (tendsto_const_pure : Tendsto _ _ (pure a)) tendsto_const_pure hu hv

/-- **Fundamental theorem of calculus-1**, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ ae μ`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f la' μ)
    (hf : Tendsto f (la' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x ∂μ) - ∫ x in u t..b, f x ∂μ) + ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  simpa using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab hmeas
      stronglyMeasurableAt_bot hf ((tendsto_bot : Tendsto _ ⊥ (𝓝 (0 : E))).mono_left inf_le_left) hu
      hv (tendsto_const_pure : Tendsto _ _ (pure b)) tendsto_const_pure

end IsLocallyFiniteMeasure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/


variable [CompleteSpace E]
  {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι} {a b : ℝ}
  {u v ua ub va vb : ι → ℝ} [FTCFilter a la la'] [FTCFilter b lb lb']

/-!
#### Auxiliary `Asymptotics.IsLittleO` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use
`Asymptotics.isLittleO` because we have no definition of `HasStrict(F)DerivAtFilter` in the library.
-/


/-- **Fundamental theorem of calculus-1**, local version.

If `f` has a finite limit `c` almost surely at `l'`, where `(l, l')` is an
`intervalIntegral.FTCFilter` pair around `a`, then `∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)`
as both `u` and `v` tend to `l`. -/
theorem integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l') (hf : Tendsto f (l' ⊓ ae volume) (𝓝 c)) {u v : ι → ℝ}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa [integral_const] using! measure_integral_sub_linear_isLittleO_of_tendsto_ae hfm hf hu hv

/-- **Fundamental theorem of calculus-1**, strict differentiability at filter in both endpoints.

If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `intervalIntegral.FTCFilter`
pair around `a`, and `(lb, lb')` is an `intervalIntegral.FTCFilter` pair around `b`, and `f` has
finite limits `ca` and `cb` almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(‖va - ua‖ + ‖vb - ub‖)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `HasStrictFDerivAtFilter` if we had this
definition. -/
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la')
    (hmeas_b : StronglyMeasurableAtFilter f lb') (ha_lim : Tendsto f (la' ⊓ ae volume) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae volume) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x) - ∫ x in ua t..ub t, f x) -
          ((vb t - ub t) • cb - (va t - ua t) • ca)) =o[lt]
      fun t => ‖va t - ua t‖ + ‖vb t - ub t‖ := by
  simpa [integral_const]
    using measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab hmeas_a hmeas_b
      ha_lim hb_lim hua hva hub hvb

/-- **Fundamental theorem of calculus-1**, strict differentiability at filter in both endpoints.

If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `intervalIntegral.FTCFilter`
pair around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(‖v - u‖)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `HasStrictDerivAtFilter` if we had this definition. -/
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f lb')
    (hf : Tendsto f (lb' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x) - ∫ x in a..u t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa only [integral_const, smul_eq_mul, mul_one] using!
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hab hmeas hf hu hv

/-- **Fundamental theorem of calculus-1**, strict differentiability at filter in both endpoints.

If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `intervalIntegral.FTCFilter`
pair around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(‖v - u‖)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `HasStrictDerivAtFilter` if we had this definition. -/
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f la')
    (hf : Tendsto f (la' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x) - ∫ x in u t..b, f x) + (v t - u t) • c) =o[lt] (v - u) := by
  simpa only [integral_const, smul_eq_mul, mul_one] using!
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left hab hmeas hf hu hv

open ContinuousLinearMap (fst snd smulRight sub_apply smulRight_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_hasStrictFDerivAt_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tends to `a` and `b`,
  respectively;

* `integral_hasStrictFDerivAt`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_hasStrictDerivAt_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_hasStrictDerivAt_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/


/-- **Fundamental theorem of calculus-1**, strict differentiability in both endpoints.

If `f : ℝ → E` is integrable on `a..b` and `f x` has finite limits `ca` and `cb` almost surely as
`x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
theorem integral_hasStrictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) := by
  have :=
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (continuous_snd.fst.tendsto ((a, b), (a, b)))
      (continuous_fst.fst.tendsto ((a, b), (a, b)))
      (continuous_snd.snd.tendsto ((a, b), (a, b)))
      (continuous_fst.snd.tendsto ((a, b), (a, b)))
  refine .of_isLittleO <| (this.congr_left ?_).trans_isBigO ?_
  · simp [sub_smul]
  · exact isBigO_fst_prod.norm_left.add isBigO_snd_prod.norm_left

/-- **Fundamental theorem of calculus-1**, strict differentiability in both endpoints.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `a` and `b`, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of
strict differentiability. -/
theorem integral_hasStrictFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost surely at `b`, then
`u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b :=
  .of_isLittleO <|
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb continuousAt_snd
      continuousAt_fst

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `b`, then `u ↦ ∫ x in a..u, f x` has
derivative `f b` at `b` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- **Fundamental theorem of calculus-1**, strict differentiability in the left endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost surely at `a`, then
`u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-c) a := by
  simpa only [← integral_symm] using
    (integral_hasStrictDerivAt_of_tendsto_ae_right hf.symm hmeas ha).fun_neg

/-- **Fundamental theorem of calculus-1**, strict differentiability in the left endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `a`, then `u ↦ ∫ x in u..b, f x` has
derivative `-f a` at `a` in the sense of strict differentiability. -/
theorem integral_hasStrictDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-f a) a := by
  simpa only [← integral_symm] using (integral_hasStrictDerivAt_right hf.symm hmeas ha).fun_neg

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is continuous, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b` in the sense
of strict differentiability. -/
theorem _root_.Continuous.integral_hasStrictDerivAt {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    HasStrictDerivAt (fun u => ∫ x : ℝ in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt

/-- **Fundamental theorem of calculus-1**, derivative in the right endpoint.

If `f : ℝ → E` is continuous, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` is `f b`. -/
theorem _root_.Continuous.deriv_integral (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u => ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `HasFDerivAt`,
`HasDerivAt`, `fderiv`, and `deriv`.
-/


/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
theorem integral_hasFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) :=
  (integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).hasFDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u •
ca` at `(a, b)`. -/
theorem integral_hasFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  (integral_hasStrictFDerivAt hf hmeas_a hmeas_b ha hb).hasFDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
theorem fderiv_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)`
equals `(u, v) ↦ v • cb - u • ca`. -/
theorem fderiv_integral (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a) :=
  (integral_hasFDerivAt hf hmeas_a hmeas_b ha hb).fderiv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has a
finite limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
theorem integral_hasDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in a..u, f x) c b :=
  (integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas hb).hasDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  (integral_hasStrictDerivAt_right hf hmeas hb).hasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem deriv_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in a..u, f x) b = c :=
  (integral_hasDerivAt_of_tendsto_ae_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem deriv_integral_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    deriv (fun u => ∫ x in a..u, f x) b = f b :=
  (integral_hasDerivAt_right hf hmeas hb).deriv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has a
finite limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
theorem integral_hasDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-c) a :=
  (integral_hasStrictDerivAt_of_tendsto_ae_left hf hmeas ha).hasDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
theorem integral_hasDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-f a) a :=
  (integral_hasStrictDerivAt_left hf hmeas ha).hasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem deriv_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in u..b, f x) a = -c :=
  (integral_hasDerivAt_of_tendsto_ae_left hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem deriv_integral_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : ContinuousAt f a) :
    deriv (fun u => ∫ x in u..b, f x) a = -f a :=
  (integral_hasDerivAt_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/


/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem integral_hasFDerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (s ×ˢ t) (a, b) := by
  have :=
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (tendsto_const_pure.mono_right FTCFilter.pure_le : Tendsto _ _ (𝓝[s] a)) tendsto_fst
      (tendsto_const_pure.mono_right FTCFilter.pure_le : Tendsto _ _ (𝓝[t] b)) tendsto_snd
  rw [← nhdsWithin_prod_eq] at this
  refine .of_isLittleO <| (this.congr_left ?_).trans_isBigO ?_
  · simp [sub_smul]
  · exact isBigO_fst_prod.norm_left.add isBigO_snd_prod.norm_left

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `ContinuousAt f _` or `ContinuousWithinAt f _ _`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem integral_hasFDerivWithinAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (ha : Tendsto f la (𝓝 <| f a))
    (hb : Tendsto f lb (𝓝 <| f b)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (s ×ˢ t) (a, b) :=
  integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

/-- An auxiliary tactic closing goals `UniqueDiffWithinAt ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
macro "uniqueDiffWithinAt_Ici_Iic_univ" : tactic =>
  `(tactic| (first | exact uniqueDiffOn_Ici _ _ self_mem_Ici |
    exact uniqueDiffOn_Iic _ _ self_mem_Iic | exact uniqueDiffWithinAt_univ (𝕜 := ℝ) (E := ℝ)))

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderivWithin ℝ (fun p ↦ ∫ x in p.1..p.2, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem fderivWithin_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ)
    (ht : UniqueDiffWithinAt ℝ t b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    fderivWithin ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (s ×ˢ t) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderivWithin <| hs.prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
theorem integral_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in a..u, f x) c s b :=
  .of_isLittleO <| integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb
    (tendsto_const_pure.mono_right FTCFilter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
theorem integral_hasDerivWithinAt_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b) : HasDerivWithinAt (fun u => ∫ x in a..u, f x) (f b) s b :=
  integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
theorem derivWithin_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
theorem derivWithin_integral_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b)
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = f b :=
  (integral_hasDerivWithinAt_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
theorem integral_hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-c) s a := by
  simp only [integral_symm b]
  exact (integral_hasDerivWithinAt_of_tendsto_ae_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (resp., right)
derivative `-f a` at `a`. -/
theorem integral_hasDerivWithinAt_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a) : HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-f a) s a :=
  integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
theorem derivWithin_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas ha).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
theorem derivWithin_integral_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a)
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -f a :=
  (integral_hasDerivWithinAt_left hf hmeas ha).derivWithin hs

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiable_integral_of_continuous (hcont : Continuous f) :
    Differentiable ℝ (fun u => ∫ x in a..u, f x) := fun _ ↦
  (integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt).differentiableAt

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiableOn_integral_of_continuous {s : Set ℝ} (hcont : Continuous f) :
    DifferentiableOn ℝ (fun u => ∫ x in a..u, f x) s :=
  (differentiable_integral_of_continuous hcont).differentiableOn

/-- This is a version of the first part of FTC for a function which is continuous on an interval.
    Credit to Aaron Liu. -/
theorem hasDerivWithinAt_of_continuousOn_interval {I : Set ℝ} [I.OrdConnected] {f : ℝ → ℝ}
    (h : ContinuousOn f I) {x₀ x : ℝ} (hx₀ : x₀ ∈ I) (hx : x ∈ I) :
    HasDerivWithinAt (fun t ↦  ∫ τ in x₀..t, f τ) (f x) I x :=
  have : intervalIntegral.FTCFilter x (nhdsWithin x I) (nhdsWithin x I) := by
    refine @intervalIntegral.FTCFilter.mk x (nhdsWithin x I) (nhdsWithin x I) ⟨?_⟩ ?_ ?_ ?_
    · rw [Filter.tendsto_smallSets_iff]
      intro t ht
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at ht
      obtain ⟨u, hu, hut⟩ := ht
      obtain ⟨a, b, haxb, habx, habu⟩ := exists_Icc_mem_subset_of_mem_nhds hu
      have hab : Set.Icc a b ∩ I ∈ nhdsWithin x I :=
    Set.inter_comm _ _ ▸ inter_mem_nhdsWithin I habx
      filter_upwards [Filter.prod_mem_prod hab hab] with (i, j) ⟨hi, hj⟩
      refine subset_trans (Set.subset_inter ?_ ?_) hut
      · refine subset_trans ?_ habu
        intro k hk
        exact ⟨hi.1.1.trans hk.1.le, hk.2.trans hj.1.2⟩
      · intro k hk
        exact Set.Icc_subset I hi.2 hj.2 (Set.Ioc_subset_Icc_self hk)
    · exact pure_le_nhdsWithin hx
    · exact nhdsWithin_le_nhds
    · exact @Filter.inf_isMeasurablyGenerated _ _ _ _ _
        (Set.OrdConnected.measurableSet ‹_›).principal_isMeasurablyGenerated
  intervalIntegral.integral_hasDerivWithinAt_right
    ((h.mono (Set.OrdConnected.uIcc_subset ‹_› hx₀ hx)).intervalIntegrable)
    (h.stronglyMeasurableAtFilter_nhdsWithin (Set.OrdConnected.measurableSet ‹_›) x)
    (h.continuousWithinAt hx)

theorem hasDerivAt_integral_of_continuousOn_open_interval {I : Set ℝ} [I.OrdConnected] {t₀ t : ℝ}
    (hI : IsOpen I) {f : ℝ → ℝ} (hf : ContinuousOn f I) (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    HasDerivAt (fun x ↦  ∫ u in t₀..x, f u) (f t) t :=
  (hasDerivWithinAt_of_continuousOn_interval hf ht₀ ht).hasDerivAt (hI.mem_nhds ht)

end FTC1

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫ x in a..b, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫ x in a..b, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫ x in a..t, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left-hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right-hand side increases by
`∫ x in t..u, G' x` which is roughly at least `∫ x in t..u, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/

section FTC2

variable {g' g φ : ℝ → ℝ} {a b : ℝ}

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `[a, b)`. -/
theorem sub_le_integral_of_hasDeriv_right_of_le_Ico (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (φint : IntegrableOn φ (Icc a b)) (hφg : ∀ x ∈ Ico a b, g' x ≤ φ x) :
    g b - g a ≤ ∫ y in a..b, φ y := by
  refine le_of_forall_pos_le_add fun ε εpos => ?_
  -- Bound from above `g'` by a lower-semicontinuous function `G'`.
  rcases exists_lt_lowerSemicontinuous_integral_lt φ φint εpos with
    ⟨G', f_lt_G', G'cont, G'int, G'lt_top, hG'⟩
  -- we will show by "induction" that `g t - g a ≤ ∫ u in a..t, G' u` for all `t ∈ [a, b]`.
  set s := {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} ∩ Icc a b
  -- the set `s` of points where this property holds is closed.
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g t - g a, ∫ u in a..t, (G' u).toReal)) (Icc a b) := by
      rw [← uIcc_of_le hab] at G'int hcont ⊢
      exact (hcont.sub continuousOn_const).prodMk (continuousOn_primitive_interval G'int)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have main : Icc a b ⊆ {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} := by
    -- to show that the set `s` is all `[a, b]`, it suffices to show that any point `t` in `s`
    -- with `t < b` admits another point in `s` slightly to its right
    -- (this is a sort of real induction).
    refine s_closed.Icc_subset_of_forall_exists_gt
      (by simp only [integral_same, mem_setOf_eq, sub_self, le_rfl]) fun t ht v t_lt_v => ?_
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ y : ℝ, (g' t : EReal) < y ∧ (y : EReal) < G' t :=
      EReal.lt_iff_exists_real_btwn.1 ((EReal.coe_le_coe_iff.2 (hφg t ht.2)).trans_lt (f_lt_G' t))
    -- bound from below the increase of `∫ x in a..u, G' x` on the right of `t`, using the lower
    -- semicontinuity of `G'`.
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫ w in t..u, (G' w).toReal := by
      have B : ∀ᶠ u in 𝓝 t, (y : EReal) < G' u := G'cont.lowerSemicontinuousAt _ _ y_lt_G'
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩
      have : Ioo t (min M b) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (lt_min hM ht.right.right)
      filter_upwards [this] with u hu
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _))
      calc
        (u - t) * y = ∫ _ in Icc t u, y := by
          simp only [MeasureTheory.integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            univ_inter, hu.left.le, Real.volume_real_Icc_of_le, smul_eq_mul]
        _ ≤ ∫ w in t..u, (G' w).toReal := by
          rw [intervalIntegral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc]
          apply setIntegral_mono_ae_restrict
          · simp
          · exact IntegrableOn.mono_set G'int I
          · have C1 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), G' x < ∞ :=
              ae_mono (Measure.restrict_mono I le_rfl) G'lt_top
            have C2 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), x ∈ Icc t u :=
              ae_restrict_mem measurableSet_Icc
            filter_upwards [C1, C2] with x G'x hx
            apply EReal.coe_le_coe_iff.1
            have : x ∈ Ioo m M := by
              simp only [hm.trans_le hx.left,
                (hx.right.trans_lt hu.right).trans_le (min_le_left M b), mem_Ioo, and_self_iff]
            refine (H this).out.le.trans_eq ?_
            exact (EReal.coe_toReal G'x.ne (f_lt_G' x).ne_bot).symm
    -- bound from above the increase of `g u - g a` on the right of `t`, using the derivative at `t`
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y := by
      have g'_lt_y : g' t < y := EReal.coe_lt_coe_iff.1 g'_lt_y'
      filter_upwards [(hderiv t ⟨ht.2.1, ht.2.2⟩).limsup_slope_le' (notMem_Ioi.2 le_rfl) g'_lt_y,
        self_mem_nhdsWithin] with u hu t_lt_u
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u.out).le
      rwa [← smul_eq_mul, sub_smul_slope] at this
    -- combine the previous two bounds to show that `g u - g a` increases less quickly than
    -- `∫ x in a..u, G' x`.
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫ w in t..u, (G' w).toReal := by
      filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b) := Ioc_mem_nhdsGT <| lt_min t_lt_v ht.2.2
    -- choose a point `x` slightly to the right of `t` which satisfies the above bound
    rcases (I3.and I4).exists with ⟨x, hx, h'x⟩
    -- we check that it belongs to `s`, essentially by construction
    refine ⟨x, ?_, Ioc_subset_Ioc le_rfl (min_le_left _ _) h'x⟩
    calc
      g x - g a = g t - g a + (g x - g t) := by abel
      _ ≤ (∫ w in a..t, (G' w).toReal) + ∫ w in t..x, (G' w).toReal := add_le_add ht.1 hx
      _ = ∫ w in a..x, (G' w).toReal := by
        apply integral_add_adjacent_intervals
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.1]
          exact IntegrableOn.mono_set G'int
            (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le))
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x.1.le]
          apply IntegrableOn.mono_set G'int
          exact Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_right _ _)))
  -- now that we know that `s` contains `[a, b]`, we get the desired result by applying this to `b`.
  calc
    g b - g a ≤ ∫ y in a..b, (G' y).toReal := main (right_mem_Icc.2 hab)
    _ ≤ (∫ y in a..b, φ y) + ε := by
      convert! hG'.le <;>
        · rw [intervalIntegral.integral_of_le hab]
          simp only [integral_Icc_eq_integral_Ioc', Real.volume_singleton]

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `(a, b)`. -/
theorem sub_le_integral_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, g' x ≤ φ x) : g b - g a ≤ ∫ y in a..b, φ y := by
  -- This follows from the version on a closed-open interval (applied to `[t, b)` for `t` close to
  -- `a`) and a continuity argument.
  obtain rfl | a_lt_b := hab.eq_or_lt
  · simp
  set s := {t | g b - g t ≤ ∫ u in t..b, φ u} ∩ Icc a b
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g b - g t, ∫ u in t..b, φ u)) (Icc a b) := by
      rw [← uIcc_of_le hab] at hcont φint ⊢
      exact (continuousOn_const.sub hcont).prodMk (continuousOn_primitive_interval_left φint)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc isClosed_le_prod
  have A : closure (Ioc a b) ⊆ s := by
    apply s_closed.closure_subset_iff.2
    intro t ht
    refine ⟨?_, ⟨ht.1.le, ht.2⟩⟩
    exact
      sub_le_integral_of_hasDeriv_right_of_le_Ico ht.2 (hcont.mono (Icc_subset_Icc ht.1.le le_rfl))
        (fun x hx => hderiv x ⟨ht.1.trans_le hx.1, hx.2⟩)
        (φint.mono_set (Icc_subset_Icc ht.1.le le_rfl)) fun x hx => hφg x ⟨ht.1.trans_le hx.1, hx.2⟩
  rw [closure_Ioc a_lt_b.ne] at A
  exact (A (left_mem_Icc.2 hab)).1

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`. -/
theorem integral_le_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, φ x ≤ g' x) : (∫ y in a..b, φ y) ≤ g b - g a := by
  rw [← neg_le_neg_iff]
  convert!
    sub_le_integral_of_hasDeriv_right_of_le hab hcont.neg (fun x hx => (hderiv x hx).neg) φint.neg
      fun x hx => neg_le_neg (hφg x hx) using 1
  · abel
  · simp only [← integral_neg]; rfl

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`: real version -/
theorem integral_eq_sub_of_hasDeriv_right_of_le_real (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'int : IntegrableOn g' (Icc a b)) : ∫ y in a..b, g' y = g b - g a :=
  le_antisymm (integral_le_sub_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)
    (sub_le_integral_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)

variable [CompleteSpace E] {f f' : ℝ → E}

/-- **Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`,
  then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g => ?_
  rw [← g.intervalIntegral_comp_comm f'int, g.map_sub]
  exact integral_eq_sub_of_hasDeriv_right_of_le_real hab (g.continuous.comp_continuousOn hcont)
    (fun x hx => g.hasFDerivAt.comp_hasDerivWithinAt x (hderiv x hx))
    (g.integrable_comp ((intervalIntegrable_iff_integrableOn_Icc_of_le hab enorm_ne_top).1 f'int))

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is integrable on `[a, b]` then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_hasDeriv_right (hcont : ContinuousOn f (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, min_eq_left, max_eq_right, hab] at hcont hderiv hint
    apply integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  · simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab] at hcont hderiv
    rw [integral_symm, integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint.symm, neg_sub]

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`) and
  has a derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`, then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_hasDerivAt_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivWithinAt)
    hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_hasDerivAt (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right (HasDerivAt.continuousOn hderiv)
    (fun _x hx => (hderiv _ (mem_Icc_of_Ioo hx)).hasDerivWithinAt) hint

theorem integral_eq_sub_of_hasDerivAt_of_tendsto (hab : a < b) {fa fb}
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    ∫ y in a..b, f' y = fb - fa := by
  set F : ℝ → E := update (update f a fa) b fb
  have Fderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f' x) x := by
    refine fun x hx => (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy
    unfold F
    rw [update_of_ne hy.2.ne, update_of_ne hy.1.ne']
  have hcont : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_diff_right, Ico_diff_left]
    refine ⟨⟨fun z hz => (hderiv z hz).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · exact fun _ => ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hab] with _ hz using (update_of_ne hz.1.ne' _ _).symm
  simpa [F, hab.ne, hab.ne'] using integral_eq_sub_of_hasDerivAt_of_le hab.le hcont Fderiv hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `[a, b]` and
its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`.

See also `integral_deriv_of_contDiffOn_Icc` for a similar theorem assuming that `f` is `C^1`. -/
theorem integral_deriv_eq_sub (hderiv : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hderiv x hx).hasDerivAt) hint

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
    (hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x) (hcont : ContinuousOn f' (uIcc a b)) :
    ∫ y in a..b, f' y = f b - f a := by
  rw [← hderiv, integral_deriv_eq_sub hdiff]
  rw [hderiv]
  exact hcont.intervalIntegrable

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `(a, b)` and
its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_eq_sub_uIoo
    (hcont : ContinuousOn f [[a, b]]) (hderiv : ∀ x ∈ uIoo a b, DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, hab, uIoo_of_le] at hcont hderiv
    rw [integral_eq_sub_of_hasDerivAt_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivAt) hint]
  · simp only [uIcc_of_ge, hab, uIoo_of_ge] at hcont hderiv
    rw [integral_symm, integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun x hx => (hderiv x hx).hasDerivAt) hint.symm, neg_sub]

/-- A variant of `intervalIntegral.integral_deriv_eq_sub`, the Fundamental theorem
of calculus, involving integrating over the unit interval. -/
lemma integral_unitInterval_deriv_eq_sub [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    {f f' : 𝕜 → E} {z₀ z₁ : 𝕜}
    (hcont : ContinuousOn (fun t : ℝ ↦ f' (z₀ + t • z₁)) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁)) :
    z₁ • ∫ t in (0 : ℝ)..1, f' (z₀ + t • z₁) = f (z₀ + z₁) - f z₀ := by
  let γ (t : ℝ) : 𝕜 := z₀ + t • z₁
  have hint : IntervalIntegrable (z₁ • (f' ∘ γ)) MeasureTheory.volume 0 1 :=
    (ContinuousOn.const_smul hcont z₁).intervalIntegrable_of_Icc zero_le_one
  have hderiv' (t) (ht : t ∈ Set.uIcc (0 : ℝ) 1) : HasDerivAt (f ∘ γ) (z₁ • (f' ∘ γ) t) t := by
    refine (hderiv t <| (Set.uIcc_of_le (α := ℝ) zero_le_one).symm ▸ ht).scomp t <| .const_add _ ?_
    simp [hasDerivAt_iff_isLittleO, sub_smul]
  convert! (integral_eq_sub_of_hasDerivAt hderiv' hint) using 1
  · simp_rw [← integral_smul, Function.comp_apply, γ]
  · simp only [γ, Function.comp_apply, one_smul, zero_smul, add_zero]

/-!
### Automatic integrability for nonnegative derivatives
-/

/-- When the right derivative of a function is nonnegative, then it is automatically integrable. -/
theorem integrableOn_deriv_right_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) : IntegrableOn g' (Ioc a b) := by
  by_cases hab : a < b; swap
  · simp [Ioc_eq_empty hab]
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have meas_g' : AEMeasurable g' (volume.restrict (Ioo a b)) := by
    apply (aemeasurable_derivWithin_Ioi g _).congr
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
    exact (hderiv x hx).derivWithin (uniqueDiffWithinAt_Ioi _)
  suffices H : (∫⁻ x in Ioo a b, ‖g' x‖₊) ≤ ENNReal.ofReal (g b - g a) from
    ⟨meas_g'.aestronglyMeasurable, H.trans_lt ENNReal.ofReal_lt_top⟩
  by_contra! H
  obtain ⟨f, fle, fint, hf⟩ :
    ∃ f : SimpleFunc ℝ ℝ≥0,
      (∀ x, f x ≤ ‖g' x‖₊) ∧
        (∫⁻ x : ℝ in Ioo a b, f x) < ∞ ∧ ENNReal.ofReal (g b - g a) < ∫⁻ x : ℝ in Ioo a b, f x :=
    exists_lt_lintegral_simpleFunc_of_lt_lintegral H
  let F : ℝ → ℝ := (↑) ∘ f
  have intF : IntegrableOn F (Ioo a b) := by
    refine ⟨f.measurable.coe_nnreal_real.aestronglyMeasurable, ?_⟩
    simpa only [F, hasFiniteIntegral_iff_enorm, comp_apply, NNReal.enorm_eq] using fint
  have A : ∫⁻ x : ℝ in Ioo a b, f x = ENNReal.ofReal (∫ x in Ioo a b, F x) :=
    lintegral_coe_eq_integral _ intF
  rw [A] at hf
  have B : (∫ x : ℝ in Ioo a b, F x) ≤ g b - g a := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    refine integral_le_sub_of_hasDeriv_right_of_le hab.le hcont hderiv ?_ fun x hx => ?_
    · rwa [integrableOn_Icc_iff_integrableOn_Ioo]
    · convert! NNReal.coe_le_coe.2 (fle x)
      simp only [Real.norm_of_nonneg (g'pos x hx), coe_nnnorm]
  exact lt_irrefl _ (hf.trans_le (ENNReal.ofReal_le_ofReal B))

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
Ioc version. -/
theorem integrableOn_deriv_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
    IntegrableOn g' (Ioc a b) :=
  integrableOn_deriv_right_of_nonneg hcont (fun x hx => (hderiv x hx).hasDerivWithinAt) g'pos

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
interval version. -/
theorem intervalIntegrable_deriv_of_nonneg (hcont : ContinuousOn g (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ g' x) : IntervalIntegrable g' volume a b := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, min_eq_left, max_eq_right, IntervalIntegrable, hab,
      Ioc_eq_empty_of_le, integrableOn_empty, and_true] at hcont hderiv hpos ⊢
    exact integrableOn_deriv_of_nonneg hcont hderiv hpos
  · simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab, IntervalIntegrable, Ioc_eq_empty_of_le,
      integrableOn_empty, true_and] at hcont hderiv hpos ⊢
    exact integrableOn_deriv_of_nonneg hcont hderiv hpos

end FTC2

end intervalIntegral

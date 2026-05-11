/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sub-exponential random variables

A real-valued random variable `X` on a measure space `(Ω, μ)` is
**`(ν, b)`-sub-exponential** if there exist nonnegative reals `ν` and `b`
such that the moment-generating function of `X` satisfies the Gaussian
bound

`mgf X μ s ≤ exp (s² · ν / 2)`

in the small-`s` regime `|s| · b < 1`. Setting `b = 0` removes the side
condition and recovers the sub-Gaussian moment-generating function bound
already formalized as `ProbabilityTheory.HasSubgaussianMGF`; the
parameter `b` thus measures how far the variable departs from
sub-Gaussian behaviour, i.e. how heavy its tails can be.

This is the standard definition used in
[wainwright2019high, §2.1.3] and [vershynin2018high, §2.7]. Combined
with the Chernoff bound `ProbabilityTheory.measure_ge_le_exp_mul_mgf`,
it yields the canonical two-regime **Bernstein inequality**

`μ.real {ω | t ≤ X ω} ≤ exp(-min(t² / (2ν), t / (2b)))`.

## Main definitions

* `ProbabilityTheory.IsSubExponential`: `X` has a `(ν, b)`-sub-exponential
  moment-generating function under `μ`.

## Main statements

* `ProbabilityTheory.IsSubExponential.const`: a constant function is
  `(0, 0)`-sub-exponential under any probability measure.
* `ProbabilityTheory.IsSubExponential.mono_b`: the sub-exponential class
  is monotone in the scale parameter `b`.
* `ProbabilityTheory.IsSubExponential.mono_nu`: the sub-exponential
  class is monotone in the variance proxy `ν`.
* `ProbabilityTheory.IsSubExponential.of_hasSubgaussianMGF`: every
  `HasSubgaussianMGF`-sub-Gaussian variable is sub-exponential with
  `b = 0`.
* `ProbabilityTheory.IsSubExponential.measure_ge_le`: the Chernoff-style
  one-sided tail bound for a sub-exponential random variable.

## Implementation notes

We do not include integrability of `exp (s · X)` in the structure, in
contrast to `Mathlib.Probability.Moments.SubGaussian`'s
`HasSubgaussianMGF`. The Chernoff tail bound
`IsSubExponential.measure_ge_le` therefore takes integrability as an
explicit hypothesis. This keeps the definition lightweight and matches
the convention used in [bach2024learning, §1.2], where the MGF
inequality alone is taken as the working definition.

## References

* [vershynin2018high] Vershynin, R. (2018).
  *High-Dimensional Probability*. Cambridge University Press. §2.7.
* [wainwright2019high] Wainwright, M. J. (2019).
  *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*. Cambridge
  University Press. §2.1.3.
* [bach2024learning] Bach, F. (2024). *Learning Theory from First
  Principles*. MIT Press. §1.2.

## Tags

sub-exponential, concentration, MGF, Bernstein
-/

namespace ProbabilityTheory

open MeasureTheory Real

@[expose] public section

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A real-valued random variable `X` on `(Ω, μ)` is
`(ν, b)`-**sub-exponential** if its moment-generating function admits the
Gaussian bound `mgf X μ s ≤ exp (s² · ν / 2)` for every real `s` lying
in the open interval `(-1/b, 1/b)`, encoded as the side condition
`|s| · b < 1`. The parameters `ν` and `b` are required to be
nonnegative.

Taking `b = 0` collapses the side condition `|s| · b < 1` to the
universally true `0 < 1`, so the MGF inequality holds for every `s : ℝ`
and we recover the sub-Gaussian moment-generating function bound. -/
structure IsSubExponential (X : Ω → ℝ) (μ : Measure Ω) (ν b : ℝ) : Prop where
  /-- The variance proxy `ν` is nonnegative. -/
  ν_nonneg : 0 ≤ ν
  /-- The scale parameter `b` is nonnegative. -/
  b_nonneg : 0 ≤ b
  /-- The MGF is bounded by a Gaussian in the small-`s` regime
  `|s| · b < 1`. -/
  mgf_le : ∀ s : ℝ, |s| * b < 1 → mgf X μ s ≤ Real.exp (s ^ 2 * ν / 2)

namespace IsSubExponential

variable {X : Ω → ℝ} {μ : Measure Ω} {ν b ν' b' : ℝ}

/-- Any constant random variable equal to `0` is `(0, 0)`-sub-exponential
under any probability measure. More generally, see `const` below. -/
theorem const_zero (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubExponential (fun _ : Ω => (0 : ℝ)) μ 0 0 where
  ν_nonneg := le_rfl
  b_nonneg := le_rfl
  mgf_le := by
    intro s _
    have hmgf : mgf (fun _ : Ω => (0 : ℝ)) μ s = 1 := by simp
    have hrhs : Real.exp (s ^ 2 * 0 / 2) = 1 := by simp
    rw [hmgf, hrhs]

/-- Enlarging the scale parameter `b` preserves the sub-exponential
property: a `(ν, b)`-sub-exponential variable is automatically
`(ν, b')`-sub-exponential whenever `b ≤ b'`. -/
theorem mono_b (h : IsSubExponential X μ ν b) (hb : b ≤ b') :
    IsSubExponential X μ ν b' where
  ν_nonneg := h.ν_nonneg
  b_nonneg := le_trans h.b_nonneg hb
  mgf_le := by
    intro s hs
    have habs : 0 ≤ |s| := abs_nonneg s
    have hmul : |s| * b ≤ |s| * b' := mul_le_mul_of_nonneg_left hb habs
    exact h.mgf_le s (lt_of_le_of_lt hmul hs)

/-- Enlarging the variance proxy `ν` preserves the sub-exponential
property: a `(ν, b)`-sub-exponential variable is automatically
`(ν', b)`-sub-exponential whenever `ν ≤ ν'`. -/
theorem mono_nu (h : IsSubExponential X μ ν b) (hν : ν ≤ ν') :
    IsSubExponential X μ ν' b where
  ν_nonneg := le_trans h.ν_nonneg hν
  b_nonneg := h.b_nonneg
  mgf_le := by
    intro s hs
    have hbound := h.mgf_le s hs
    have hsq : 0 ≤ s ^ 2 := sq_nonneg s
    have hrhs : s ^ 2 * ν / 2 ≤ s ^ 2 * ν' / 2 := by
      have := mul_le_mul_of_nonneg_left hν hsq
      linarith
    exact le_trans hbound (Real.exp_le_exp.mpr hrhs)

/-! ## Relationship to sub-Gaussian variables

A `(ν, 0)`-sub-exponential variable is exactly a variable whose
moment-generating function is bounded by `exp (s² · ν / 2)` for every
`s : ℝ`. This is the defining MGF inequality of the sub-Gaussian class
`ProbabilityTheory.HasSubgaussianMGF` (modulo the additional
integrability requirement that `HasSubgaussianMGF` packages into the
structure). The scale parameter `b ≥ 0` therefore quantifies how far
`X` departs from sub-Gaussian behaviour: as `b` grows the heavy-tail
regime `|s| · b ≥ 1` excluded from the MGF bound widens.

The lemma below converts a `HasSubgaussianMGF`-sub-Gaussian variable
into a sub-exponential variable with `b = 0` by simply forgetting the
integrability part of the sub-Gaussian structure.
-/

/-- Every `c`-sub-Gaussian random variable (in the sense of
`ProbabilityTheory.HasSubgaussianMGF`) is `(c, 0)`-sub-exponential. The
scale parameter `b = 0` removes the side condition, so the MGF bound
holds for every `s : ℝ`. -/
theorem of_hasSubgaussianMGF {X : Ω → ℝ} {μ : Measure Ω} {c : NNReal}
    (h : HasSubgaussianMGF X c μ) :
    IsSubExponential X μ (c : ℝ) 0 where
  ν_nonneg := c.coe_nonneg
  b_nonneg := le_rfl
  mgf_le := by
    intro s _
    have hbound : mgf X μ s ≤ Real.exp ((c : ℝ) * s ^ 2 / 2) := h.mgf_le s
    have hcomm : (c : ℝ) * s ^ 2 / 2 = s ^ 2 * (c : ℝ) / 2 := by ring
    rw [hcomm] at hbound
    exact hbound

/-- **Chernoff bound for sub-exponential random variables.**

For a `(ν, b)`-sub-exponential random variable `X`, every nonnegative
parameter `s` in the small-`s` regime `s · b < 1` gives the tail bound

`μ.real {ω | ε ≤ X ω} ≤ exp(-s · ε + s² · ν / 2)`.

The optimal choice `s = ε / ν` (when `0 ≤ ε ≤ ν / b`) yields the
"sub-Gaussian regime" of Bernstein's inequality
`μ.real {ω | ε ≤ X ω} ≤ exp(-ε² / (2ν))`, while the boundary choice
`s ↑ 1/b` yields the "exponential regime"
`μ.real {ω | ε ≤ X ω} ≤ exp(-ε / (2b))`. Combining the two regimes
recovers the canonical Bernstein bound; we leave that optimization to
the caller. -/
theorem measure_ge_le [IsFiniteMeasure μ]
    (h : IsSubExponential X μ ν b) (ε s : ℝ) (hs : 0 ≤ s) (hsb : s * b < 1)
    (h_int : Integrable (fun ω => Real.exp (s * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-s * ε + s ^ 2 * ν / 2) := by
  -- Step 1: classical Chernoff bound from Mathlib.
  have hChernoff : μ.real {ω | ε ≤ X ω} ≤ Real.exp (-s * ε) * mgf X μ s :=
    measure_ge_le_exp_mul_mgf ε hs h_int
  -- Step 2: bound the MGF using `h.mgf_le`. The side condition
  -- `|s| * b < 1` follows from `s ≥ 0` and `s * b < 1`.
  have habs : |s| = s := abs_of_nonneg hs
  have hsb' : |s| * b < 1 := by rw [habs]; exact hsb
  have hmgf : mgf X μ s ≤ Real.exp (s ^ 2 * ν / 2) := h.mgf_le s hsb'
  -- Step 3: chain the two bounds and fold the exponents.
  have hexp_pos : 0 < Real.exp (-s * ε) := Real.exp_pos _
  have hstep :
      Real.exp (-s * ε) * mgf X μ s ≤
        Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / 2) :=
    mul_le_mul_of_nonneg_left hmgf hexp_pos.le
  have hfold :
      Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / 2) =
        Real.exp (-s * ε + s ^ 2 * ν / 2) := by
    rw [← Real.exp_add]
  calc μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-s * ε) * mgf X μ s := hChernoff
    _ ≤ Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / 2) := hstep
    _ = Real.exp (-s * ε + s ^ 2 * ν / 2) := hfold

end IsSubExponential

/-! ## Examples -/

section Examples

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Example: the constantly zero random variable is sub-exponential with
parameters `(0, 0)` under any probability measure. -/
example (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubExponential (fun _ : Ω => (0 : ℝ)) μ 0 0 :=
  IsSubExponential.const_zero μ

/-- Example: monotonicity in `b` lets us weaken the scale parameter on
demand. The zero variable is sub-exponential with parameters
`(0, 5)` for any nonnegative `b`. -/
example (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubExponential (fun _ : Ω => (0 : ℝ)) μ 0 5 :=
  (IsSubExponential.const_zero μ).mono_b (by norm_num)

/-- Example: every `HasSubgaussianMGF`-sub-Gaussian variable is
sub-exponential with scale parameter `b = 0`. -/
example {X : Ω → ℝ} {μ : Measure Ω} {c : NNReal}
    (h : HasSubgaussianMGF X c μ) :
    IsSubExponential X μ (c : ℝ) 0 :=
  IsSubExponential.of_hasSubgaussianMGF h

end Examples

end

end ProbabilityTheory

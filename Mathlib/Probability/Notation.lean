/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|m]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|m]` for a measure `P` is defined in
  `MeasureTheory.Function.ConditionalExpectation.Basic`.
- `P⟦s|m⟧ = P[s.indicator (fun ω => (1 : ℝ)) | m]`, conditional probability of a set.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rnDeriv Q`
We note that the notation `∂P/∂Q` applies to three different cases, namely,
`MeasureTheory.Measure.rnDeriv`, `MeasureTheory.SignedMeasure.rnDeriv` and
`MeasureTheory.ComplexMeasure.rnDeriv`.

- `ℙ` is a notation for `volume` on a measured space.

To use these notations, you need to use `open scoped ProbabilityTheory`
or `open ProbabilityTheory`.
-/


open MeasureTheory

open scoped MeasureTheory

/-- `𝔼[f|m]` is the conditional expectation of `f` with respect to `m`. -/
scoped[ProbabilityTheory] notation "𝔼[" X "|" m "]" =>
  MeasureTheory.condExp m MeasureTheory.MeasureSpace.volume X

-- `scoped[ProbabilityTheory]` isn't legal for `macro`s.
namespace ProbabilityTheory
/-- `P[X]` is the expectation of `X` under the measure `P`.

Note that this notation can conflict with the `GetElem` notation for lists. Usually if you see an
error about ambiguous notation when trying to write `l[i]` for a list, it means that Lean could
not find `i < l.length`, and so fell back to trying this notation as well. -/
scoped macro:max P:term noWs "[" X:term "]" : term => `(∫ x, ↑($X x) ∂$P)
end ProbabilityTheory

/-- `𝔼[X]` is the expectation of `X`, defined as its Lebesgue integral. -/
scoped[ProbabilityTheory] notation "𝔼[" X "]" => ∫ a, (X : _ → _) a

/-- `P⟦s|m⟧` is the conditional expectation of `s` with respect to `m` under measure `P`. -/
scoped[ProbabilityTheory] notation P "⟦" s "|" m "⟧" =>
  MeasureTheory.condExp m P (Set.indicator s fun ω => (1 : ℝ))

/-- `X =ₐₛ Y` if `X = Y` almost surely. -/
scoped[ProbabilityTheory] notation:50 X " =ₐₛ " Y:50 => X =ᵐ[MeasureTheory.MeasureSpace.volume] Y

/-- `X ≤ₐₛ Y` if `X ≤ Y` almost surely. -/
scoped[ProbabilityTheory] notation:50 X " ≤ₐₛ " Y:50 => X ≤ᵐ[MeasureTheory.MeasureSpace.volume] Y

/-- `∂P/∂Q` is the Radon–Nikodym derivative of `P` with respect to `Q`. -/
scoped[ProbabilityTheory] notation "∂" P "/∂" Q:100 => MeasureTheory.Measure.rnDeriv P Q

/-- `ℙ` is a notation for `volume` on a measured space. -/
scoped[ProbabilityTheory] notation "ℙ" => MeasureTheory.MeasureSpace.volume

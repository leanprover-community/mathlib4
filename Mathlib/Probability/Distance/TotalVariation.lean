/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-!
# Total variation distance between two measures

The **total variation distance** between two (finite) measures `μ` and `ν` on a
measurable space `α` is a fundamental quantity in probability and information
theory: it measures how far apart the two measures are when viewed as set
functions, and it is the basis for many classical inequalities such as
Pinsker, Bretagnolle–Huber, and the Le Cam two-point lower bound.

This file gives a named definition `tvDist μ ν` for this distance, in terms
of Mathlib's existing truncated subtraction `μ - ν` on measures (see
`Mathlib.MeasureTheory.Measure.Sub`), and proves its basic algebraic
properties. The module is deliberately self-contained: it does not depend
on the signed Jordan decomposition, keeping the import surface minimal.

## Main definitions

* `MeasureTheory.tvDist μ ν` : the total variation distance between two
  measures, defined as `((μ - ν) + (ν - μ)) Set.univ / 2`. The result lies
  in `ℝ≥0∞`, so nonnegativity is automatic and the definition extends
  naturally to infinite measures (where it may take the value `∞`).

## Main results

* `tvDist_self`   : `tvDist μ μ = 0`. Marked `@[simp]`.
* `tvDist_comm`   : `tvDist μ ν = tvDist ν μ`.
* `tvDist_nonneg` : `0 ≤ tvDist μ ν` (automatic in `ℝ≥0∞`, exposed as a
  named lemma for use in `gcongr`/rewriting chains).
* `tvDist_le_one` : for two probability measures the distance is at most `1`.
* `tvDist_eq_signedMeasure_totalVariation` : for finite measures, `tvDist μ ν`
  agrees with `½ · ‖μ.toSignedMeasure - ν.toSignedMeasure‖_TV`, where the
  right-hand side uses Mathlib's existing
  `MeasureTheory.SignedMeasure.totalVariation`. This bridges the present
  definition with the signed-measure infrastructure in
  `Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`.

## Implementation notes

We choose the formulation `((μ - ν) + (ν - μ)) Set.univ / 2` because:

1. it is manifestly symmetric in `μ` and `ν`;
2. it lives in `ℝ≥0∞`, so nonnegativity and `0 ≤ ⊤` are free;
3. it reuses the existing `Measure.sub_self` and `Measure.sub_le` simp
   lemmas, keeping the basic API one-liners;
4. it makes the basic properties (`tvDist_self`, `tvDist_comm`, `tvDist_le_one`)
   provable without invoking the Jordan decomposition.

The bridge lemma `tvDist_eq_signedMeasure_totalVariation` then connects this
formulation to Mathlib's existing
`MeasureTheory.SignedMeasure.totalVariation` for finite measures, using
`Measure.toJordanDecomposition_toSignedMeasure_sub` from
`Mathlib/MeasureTheory/VectorMeasure/Decomposition/JordanSub.lean`, which
identifies the Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure`
with the pair `(μ - ν, ν - μ)` of truncated differences. Through this bridge,
downstream results stated in terms of the existing
`SignedMeasure.totalVariation` API (such as the classical
`sup_{A measurable} |μ A - ν A|` characterization) transfer to `tvDist` for
finite measures.

The characterization `tvDist μ ν = 0 ↔ μ = ν` for finite measures is not
included in this file but is now reachable: the bridge lemma
`tvDist_eq_signedMeasure_totalVariation` reduces it to a statement about
`SignedMeasure.totalVariation` vanishing, which together with the Jordan
decomposition pins down `μ.toSignedMeasure = ν.toSignedMeasure`, hence
`μ = ν` by `Measure.toSignedMeasure_eq_toSignedMeasure_iff`. We leave this
characterization to a follow-up so that the present file stays focused on
the basic API.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University
  Press, 1998, Chapter 25.
* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern
  Recognition*, Springer, 1996, Chapter 8.

## Tags

total variation, total variation distance, statistical distance,
probability measure, finite measure
-/

@[expose] public section

namespace MeasureTheory

open ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The **total variation distance** between two measures `μ` and `ν` on a
measurable space `α`, defined as
`tvDist μ ν = ((μ - ν) + (ν - μ)) Set.univ / 2`.

For finite measures this matches the standard textbook definition
`½ · ‖μ - ν‖_TV`; for two probability measures it lies in `[0, 1]`
(see `tvDist_le_one`). The result is valued in `ℝ≥0∞` so that
nonnegativity is automatic and the definition extends naturally to
infinite measures, where it may take the value `∞`. -/
noncomputable def tvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ((μ - ν) + (ν - μ)) Set.univ / 2

/-- The total variation distance from a measure to itself vanishes. -/
@[simp]
theorem tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  simp [tvDist]

/-- The total variation distance is symmetric in its two arguments. -/
theorem tvDist_comm (μ ν : Measure α) : tvDist μ ν = tvDist ν μ := by
  simp [tvDist, add_comm]

/-- The total variation distance is nonnegative. This is automatic since
`tvDist` is valued in `ℝ≥0∞`, but the lemma is provided as a named entry
point for `gcongr`, `positivity`-style proofs, and downstream rewriting. -/
theorem tvDist_nonneg (μ ν : Measure α) : 0 ≤ tvDist μ ν :=
  bot_le

/-- For two probability measures the total variation distance is bounded by
one. The proof uses `Measure.sub_le : μ - ν ≤ μ` to bound each truncated
difference by the total mass of the corresponding probability measure,
and then divides by `2`. -/
theorem tvDist_le_one (μ ν : ProbabilityMeasure α) :
    tvDist (μ : Measure α) (ν : Measure α) ≤ 1 := by
  classical
  set μ' : Measure α := (μ : Measure α)
  set ν' : Measure α := (ν : Measure α)
  -- Each truncated difference is bounded by the corresponding measure.
  have h₁ : (μ' - ν') Set.univ ≤ μ' Set.univ :=
    Measure.sub_le (μ := μ') (ν := ν') Set.univ
  have h₂ : (ν' - μ') Set.univ ≤ ν' Set.univ :=
    Measure.sub_le (μ := ν') (ν := μ') Set.univ
  have hμ : μ' Set.univ = 1 := measure_univ
  have hν : ν' Set.univ = 1 := measure_univ
  -- Add the two pointwise bounds and rewrite the totals.
  have hsum :
      ((μ' - ν') + (ν' - μ')) Set.univ ≤ μ' Set.univ + ν' Set.univ := by
    simpa [Measure.add_apply] using add_le_add h₁ h₂
  have hsum' : ((μ' - ν') + (ν' - μ')) Set.univ ≤ 2 := by
    have h2 : μ' Set.univ + ν' Set.univ = 2 := by
      rw [hμ, hν]; norm_num
    rw [h2] at hsum
    exact hsum
  -- Divide by 2.
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  calc tvDist μ' ν'
      = ((μ' - ν') + (ν' - μ')) Set.univ / 2 := rfl
    _ ≤ 2 / 2 := ENNReal.div_le_div_right hsum' 2
    _ = 1 := ENNReal.div_self h2ne h2top

/-- For finite measures, `tvDist μ ν` agrees with `½ · ‖μ.toSignedMeasure -
ν.toSignedMeasure‖_TV`, where the right-hand side uses Mathlib's existing
`MeasureTheory.SignedMeasure.totalVariation`.

This is how `tvDist` relates to the signed-measure infrastructure in
`Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`. The proof
reduces to `MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub`,
which identifies the Jordan decomposition of
`μ.toSignedMeasure - ν.toSignedMeasure` with the pair
`(μ - ν, ν - μ)` of truncated differences in `Measure α`. -/
theorem tvDist_eq_signedMeasure_totalVariation
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν =
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ / 2 := by
  unfold tvDist
  congr 1
  -- Both sides equal `((μ - ν) + (ν - μ)) Set.univ`.
  -- The right-hand side uses Mathlib's Jordan-decomposition computation.
  rw [SignedMeasure.totalVariation,
    Measure.toJordanDecomposition_toSignedMeasure_sub,
    Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
    Measure.jordanDecompositionOfToSignedMeasureSub_negPart]

end MeasureTheory

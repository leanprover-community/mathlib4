/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.NumberTheory.NewtonPolygon.Basic
public import Mathlib.NumberTheory.NewtonPolygon.Construction
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Getting Newton polygons from the construction

Given `Construction.lean`, we construct one sided Newton polygons from a sequnce `v`.
When `v` corresponds to an additive valuation on the coefficient ring of a power series we get our
standard Newton polygon attatched to the power series.

# Main definitions and Theorems

`NewtonPolygon₀.construction` is the constructed one sided Newton polygon from a sequence `v`.

`NewtonPolygon₀.ofPowerSeries` is the constructed on sided Newton polygon attatched to a power
series `f` whose coefficients have a function `v : R → WithTop Γ`.

`NewtonPolygon₀.ofPowerSeries_isfinite` says that the constructed newton polygon from a power
series if finite exactly when the algorithm terminates
(`NewtonPolygon₀.Construction.IsFinite (coeffSeq val f)`).

-/

@[expose] public section

variable {Γ : Type*} {R : Type*} [Semiring R]

open NewtonPolygon₀.Construction

variable [CommSemiring Γ] [Algebra Γ ℝ]

/-- The one-sided Newton polygon (`NewtonPolygon₀`) attached to a coefficient-valuation sequence
`v : ℕ → WithTop Γ` by the algorithm in `Construction.lean`: `stream'_numSegments v` many
segments carrying the constructed slopes and lengths, anchored at the first coefficient of finite
valuation (with the junk anchor `(0, 0)` if there is none). All structure obligations are
discharged by the `numSegments` API from `Construction.lean`. -/
noncomputable
def NewtonPolygon₀.construction (v : ℕ → WithTop Γ) : NewtonPolygon₀ (Γ := Γ) where
  support := stream'_numSegments v
  slopes := stream'_slopes v
  slopes_junk := fun _ h => stream'_slopes_junk v h
  slopes_nonFinal := fun _ h => stream'_slopes_nonFinal v h
  slopes_final := fun _ h => stream'_slopes_final v h.1 h.2
  slopes_increasing := stream'_slopes_mono v
  lengths := stream'_lengths v
  lengths_junk := fun _ h => stream'_lengths_junk v h
  lengths_nonFinal := fun _ h => stream'_lengths_nonFinal v h
  lengths_final := fun _ h => stream'_lengths_final v h.1 h.2
  starting_point :=
    match findFirstFinite v 0 with
    | some (i, c) => ((i : ℤ), c)
    | none => (0, 0)

lemma NewtonPolygon₀.construction_isFinite {v : ℕ → WithTop Γ}
    (h : NewtonPolygon₀.Construction.IsFinite v) : (NewtonPolygon₀.construction v).IsFinite := by
  classical
  obtain ⟨n, hn⟩ := h
  simp only [NewtonPolygon₀.IsFinite, construction, stream'_numSegments]
  split_ifs with h₁ h₂
  · exact WithTop.natCast_ne_top _
  · exact WithTop.natCast_ne_top _
  · exact absurd ⟨n, hn⟩ h₂

/-- The coefficient-valuation sequence of a power series `f`. -/
noncomputable
def coeffSeq (val : R → WithTop Γ) (f : PowerSeries R) : ℕ → WithTop Γ :=
  fun i => val (PowerSeries.coeff i f)

omit [CommSemiring Γ] [Algebra Γ ℝ] in
@[simp]
lemma coeffSeq_apply (val : R → WithTop Γ) (f : PowerSeries R) (i : ℕ) :
    coeffSeq val f i = val (PowerSeries.coeff i f) := rfl

/-- The one-sided Newton polygon of a power series `f`: the polygon of its coefficient-valuation
sequence `coeffSeq val f`. -/
noncomputable
def NewtonPolygon₀.ofPowerSeries (val : R → WithTop Γ) (f : PowerSeries R) :
    NewtonPolygon₀ (Γ := Γ) :=
  construction (coeffSeq val f)

lemma NewtonPolygon₀.ofPowerSeries_isFinite {val : R → WithTop Γ} {f : PowerSeries R}
    (h : NewtonPolygon₀.Construction.IsFinite (coeffSeq val f)) :
    (NewtonPolygon₀.ofPowerSeries val f).IsFinite :=
  construction_isFinite h

/-- The (doubly-infinite) Newton polygon of a power series: its one-sided polygon embedded via
`NewtonPolygon₀.toNewtonPolygon`. -/
noncomputable
def NewtonPolygon.ofPowerSeries (val : R → WithTop Γ) (f : PowerSeries R) :
    NewtonPolygon (Γ := Γ) :=
  (NewtonPolygon₀.ofPowerSeries val f).toNewtonPolygon

end

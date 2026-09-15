/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Tactic.IntervalCases

/-!
# A finite path coherence expression

The explicit trigonometric expression and its regularization using `Real.sinc`.
-/

@[expose] public section

noncomputable section

open Real
open Filter
open scoped Topology

namespace Real.FinitePath

/-- The number of vertices plus one, as a real number. -/
noncomputable def size (d : ℕ) : ℝ := (d : ℝ) + 1

/-- The angle pi divided by the number of vertices plus one. -/
noncomputable def angle (d : ℕ) : ℝ := π / size d

/-- The squared finite path coherence expression. -/
noncomputable def coherenceSq (d : ℕ) : ℝ :=
  2 * ((d : ℝ) - 1) / (size d * Real.cos (angle d) ^ 2) *
    (((size d ^ 2 + 2) / 6) * Real.sin (angle d) ^ 2 - 1)

/-- The nonnegative square root of finite path coherence squared. -/
noncomputable def coherence (d : ℕ) : ℝ := Real.sqrt (coherenceSq d)

/-- The limiting value of the finite path coherence sequence. -/
noncomputable def coherenceLimit : ℝ := Real.sqrt (π ^ 2 / 3 - 2)

/-- The finite path coherence minus one. -/
noncomputable def gap (d : ℕ) : ℝ := coherence d - 1

/-- The limiting coherence minus one. -/
noncomputable def gapLimit : ℝ := coherenceLimit - 1

/-- The first-order expression for the limiting gap. -/
noncomputable def firstOrderGap (d : ℕ) : ℝ :=
  gapLimit - coherenceLimit / size d

theorem coherenceSq_def (d : ℕ) :
    coherenceSq d =
      2 * ((d : ℝ) - 1) / (size d * Real.cos (angle d) ^ 2) *
        (((size d ^ 2 + 2) / 6) * Real.sin (angle d) ^ 2 - 1) := rfl

theorem coherenceSq_eq_sinc (d : ℕ) :
    coherenceSq d =
      2 * (1 - 2 / size d) / Real.cos (angle d) ^ 2 *
        ((π ^ 2 * Real.sinc (angle d) ^ 2 +
          2 * Real.sin (angle d) ^ 2) / 6 - 1) := by
  have hN : size d ≠ 0 := by
    unfold size
    positivity
  have ht : angle d ≠ 0 := by
    unfold angle
    exact div_ne_zero Real.pi_ne_zero hN
  rw [coherenceSq, Real.sinc_of_ne_zero ht]
  unfold angle size
  field_simp
  ring

end Real.FinitePath

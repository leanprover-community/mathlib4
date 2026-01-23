/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: (ported/adapted for this repository)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
## Cartan/minimum-modulus helpers (stubbed API)

This repository previously imported `PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanBound`.
In this workspace we provide the small API surface that downstream files currently use:
`LogSingularity.φ`, `LogSingularity.Cφ`, and the basic facts `φ_nonneg`, `Cφ_pos`.

The heavy Cartan/minimum-modulus lemmas live elsewhere; this file is intentionally minimal.
-/

noncomputable section

namespace LogSingularity

open Real

/-- A nonnegative "log-singularity" majorant. The precise choice is not important for the
bookkeeping lemma that only needs `0 ≤ φ t`. -/
def φ (t : ℝ) : ℝ := max 0 (Real.log (1 + |t|))

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by
  simp [φ]

/-- A positive constant used in bounds for sums of `φ`. -/
def Cφ : ℝ := 1

lemma Cφ_pos : 0 < Cφ := by
  norm_num [Cφ]

end LogSingularity

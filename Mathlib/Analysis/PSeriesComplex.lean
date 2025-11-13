/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Convergence of `p`-series (complex case)

Here we show convergence of `∑ n : ℕ, 1 / n ^ p` for complex `p`. This is done in a separate file
rather than in `Analysis.PSeries` in order to keep the prerequisites of the former relatively light.

## Tags

p-series, Cauchy condensation test
-/

lemma Complex.summable_one_div_nat_cpow {p : ℂ} :
    Summable (fun n : ℕ ↦ 1 / (n : ℂ) ^ p) ↔ 1 < re p := by
  rw [← Real.summable_one_div_nat_rpow, ← summable_nat_add_iff 1 (G := ℝ),
    ← summable_nat_add_iff 1 (G := ℂ), ← summable_norm_iff]
  simp only [norm_div, norm_one, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
    (Nat.cast_pos.mpr <| Nat.succ_pos _)]

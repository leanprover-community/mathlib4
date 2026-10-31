/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

/-!
# `Real.rpow` extension for tactic `dyadic_interval`

This file implements `Real.rpow` extension for the tactic `dyadic_interval`.
-/

public section

namespace Inclusion

namespace IntervalDyadicReal

/-- Computes an enclosure of `x ^ y` for `x ∈ I` and `y ∈ J` with precision `prec`. -/
@[expose]
def rpow (I J : Interval Dyadic) (prec : ℕ) : Interval Dyadic :=
  if 0 < I.lb then exp ((I.log (prec + 1)).mul J) (prec + 1) else .univ Dyadic

@[inclusion_op interval_dyadic_real]
theorem rpow_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) (prec : ℕ) :
    x ^ y ∈ rpow I J prec := by
  unfold rpow
  split_ifs with hlb
  · obtain ⟨l, hlb, hl⟩ : ∃ l : Dyadic, I.lb = l ∧ (0 : WithBot Dyadic) < l :=
      WithBot.lt_iff_exists_coe.mp hlb
    suffices 0 < x from Real.rpow_def_of_pos this y ▸
      exp_mem (mul_mem (log_mem (prec + 1) hx) hy) (prec + 1)
    simpa using Dyadic.toReal_lt_toReal.mpr (WithBot.coe_lt_coe.mp hl) |>.trans_le <|
      Interval.mem_map_iff Dyadic.toReal |>.mp (mem_iff_mem_map.mp hx) |>.left l hlb
  · simpa [mem_iff_mem_map] using Interval.mem_map_univ Dyadic.toReal (x ^ y)

end IntervalDyadicReal

end Inclusion

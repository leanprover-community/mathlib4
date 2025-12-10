/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the tanh function

In this file we define an inverse of tanh as a function from (-1, 1) to ℝ.

## Main definitions

- `Real.artanh`: An inverse function of `Real.tanh` as a function from (-1, 1) to ℝ.

- `Real.tanhPartialEquiv`: `Real.tanh` as a `PartialEquiv`.

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `artanh` is defined using a logarithm, `arcosh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
def artanh (x : ℝ) :=
  log √((1 + x) / (1 - x))

theorem exp_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : exp (artanh x) = √((1 + x) / (1 - x)) :=
  exp_log <| sqrt_pos_of_pos <| div_pos (neg_lt_iff_pos_add'.mp hx.1) (sub_pos.mpr hx.2)

@[simp]
theorem artanh_zero : artanh 0 = 0 := by simp [artanh]

/-- `artanh` is the right inverse of `tanh` over (-1, 1). -/
theorem tanh_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : tanh (artanh x) = x := by
  rw [artanh, tanh_eq, exp_neg, exp_log, sqrt_div, inv_div]
  sorry

theorem sinh_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : sinh (artanh x) = x / √(1 - x ^ 2) := by
  rw [artanh, sinh_eq, exp_neg, exp_log]
  sorry

theorem cosh_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : cosh (artanh x) = 1 / √(1 - x ^ 2) := by
  rw [artanh, cosh_eq, exp_neg, exp_log]
  sorry

/-- `artanh` is the left inverse of `tanh`. -/
theorem artanh_tanh (x : ℝ) : artanh (tanh x) = x := by
  sorry

end Real

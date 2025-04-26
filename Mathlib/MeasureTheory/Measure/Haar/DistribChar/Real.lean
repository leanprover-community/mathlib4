/-
Copyright (c) 2024 Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Javier López-Contreras
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The distributive Haar character of `ℝ`

This file computes `distribHaarChar` in the case of the action of `ℝˣ` on `ℝ`.

This lets us know what `volume (x • s)` is in terms of `‖x‖` and `volume s`, when `x` is a
real number and `s` is a set of real numbers.

## Main declarations

* `distribHaarChar_real`: `distribHaarChar ℝ` is the usual norm on `ℝ`.
* `Real.volume_real_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℝ` and `s : Set ℝ`.
-/

open Real Complex MeasureTheory Measure Set
open scoped Pointwise

lemma Real.volume_real_smul (x : ℝ) (s : Set ℝ) : volume (x • s) = ‖x‖₊ * volume s := by
  simp [← enorm_eq_ofReal_abs, enorm_eq_nnnorm]

/-- The distributive Haar character of the action of `ℝˣ` on `ℝ` is the usual norm.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℝ` and `s : Set ℝ`.
See `Real.volume_real_smul`. -/
lemma distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊ :=
  -- We compute that `volume (x • [0, 1]) = ‖x‖₊ * volume [0, 1]`.
  distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp).ne' isCompact_Icc.measure_ne_top
      (Real.volume_real_smul ..)

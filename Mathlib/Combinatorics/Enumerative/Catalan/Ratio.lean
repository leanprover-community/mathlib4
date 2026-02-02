/-
Copyright (c) 2026 Pavel Grigorenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Grigorenko
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Analysis.SpecificLimits.Basic

/-!
## The ratio of subsequent catalan numbers

## Main results

* The explicit formula for `catalan (n + 1) / catalan n` (expressed without `Nat` division)
  and its limit as `n -> inf`.

## TODO

* Prove that assymptotically C(n) ~ 4 ^ n / (n^(3/2) sqrt pi)

-/
@[expose] public section

/--
The ratio `catalan (n + 1) / catalan n` is precisely `2 * (2 n + 1) / (n + 1)`.
-/
lemma catalan_succ_ratio (n : ℕ) : (4 * n + 2) * catalan n = (n + 2) * catalan (n + 1) := by
  rw [succ_mul_catalan_eq_centralBinom, Nat.mul_comm, ← @Nat.mul_right_inj (n + 1),
      ← Nat.mul_assoc, succ_mul_catalan_eq_centralBinom, Nat.succ_mul_centralBinom_succ]
    <;> grind

private lemma catalan_ratio_eq (n : ℕ) :
    mkRat (catalan n.succ) (catalan n) = mkRat (Nat.cast <| 4 * n + 2) (n + 2) := by
  rw [Rat.mkRat_eq_iff, Int.ofNat_mul_ofNat, Int.ofNat_mul_ofNat, Nat.cast_inj]
  · rw [Nat.mul_comm, catalan_succ_ratio]
  · simp
  · simp

open Filter

/--
The ratio of `catalan (n + 1) / catalan n` tends to `4` as `n` tends to infinity.
-/
theorem catalan_ratio_limit :
    Tendsto (fun n ↦ mkRat (catalan n.succ) (catalan n) : ℕ → ℝ) atTop (nhds (4 : ℝ)) := by
  rw [(by rw [div_one]: (4 : ℝ) = (4 / 1: ℝ))]
  apply Tendsto.congr
  rotate_left
  · exact tendsto_add_mul_div_add_mul_atTop_nhds 2 2 4 (by simp)
  · intro x
    rw [catalan_ratio_eq, Rat.mkRat_eq_div]
    simp
    grind

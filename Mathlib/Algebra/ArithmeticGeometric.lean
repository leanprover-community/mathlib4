/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Arithmetic-geometric sequences

An arithmetic-geometric sequence is a sequence defined by the recurrence relation
`u (n + 1) = a * u n + b`.

## Main statements

For a sequence `u` that satisfies the recurrence relation, we have:

* `arithmeticGeometric_eq`: for `a ≠ 1`, `u n = a ^ n * (u 0 - (b / (1 - a))) + b / (1 - a)`
* `tendsto_arithmeticGeometric_atTop`: if `1 < a` and `b / (1 - a) < u 0`, then `u n` tends to
  `+∞` as `n` tends to `+∞`.
* `arithmeticGeometric_strictMono`: if `1 < a` and `b / (1 - a) < u 0`, then `u` is strictly
  monotone.

-/

open Filter Topology

variable {R : Type*} [Field R] {u : ℕ → R} {a b : R}

lemma arithmeticGeometric_eq (hu : ∀ n, u (n + 1) = a * u n + b) (ha : a ≠ 1) (n : ℕ) :
    u n = a ^ n * (u 0 - (b / (1 - a))) + b / (1 - a) := by
  induction n with
  | zero => simp
  | succ n hn => grind

lemma arithmeticGeometric_eq' (hu : ∀ n, u (n + 1) = a * u n + b) (ha : a ≠ 1) :
    u = fun n ↦ a ^ n * (u 0 - (b / (1 - a))) + b / (1 - a) := by
  ext
  exact arithmeticGeometric_eq hu ha _

variable [LinearOrder R] [IsStrictOrderedRing R]

lemma div_lt_arithmeticGeometric (hu : ∀ n, u (n + 1) = a * u n + b)
    (ha_pos : 0 < a) (ha_ne : a ≠ 1) (h0 : b / (1 - a) < u 0) (n : ℕ) :
    b / (1 - a) < u n := by
  induction n with
  | zero => exact h0
  | succ n hn =>
    rw [hu]
    calc b / (1 - a)
    _ = a * (b / (1 - a)) + b := by grind
    _ < a * u n + b := by gcongr

lemma arithmeticGeometric_strictMono (hu : ∀ n, u (n + 1) = a * u n + b) (ha : 1 < a)
    (h0 : b / (1 - a) < u 0) :
    StrictMono u := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [hu]
  have h_lt : b / (1 - a) < u n := div_lt_arithmeticGeometric hu (by positivity) ha.ne' h0 n
  rw [div_lt_iff_of_neg (sub_neg.mpr ha)] at h_lt
  linarith

lemma tendsto_arithmeticGeometric_atTop_of_one_lt [Archimedean R]
    (hu : ∀ n, u (n + 1) = a * u n + b) (ha : 1 < a) (h0 : b / (1 - a) < u 0) :
    Tendsto u atTop atTop := by
  rw [arithmeticGeometric_eq' hu ha.ne']
  refine tendsto_atTop_add_const_right _ _ ?_
  refine Tendsto.atTop_mul_const (sub_pos.mpr h0) ?_
  exact tendsto_pow_atTop_atTop_of_one_lt ha

lemma tendsto_arithmeticGeometric_nhds_of_lt_one
    [Archimedean R] [TopologicalSpace R] [OrderTopology R]
    (hu : ∀ n, u (n + 1) = a * u n + b) (ha_pos : 0 ≤ a) (ha : a < 1) :
    Tendsto u atTop (𝓝 (b / (1 - a))) := by
  rw [arithmeticGeometric_eq' hu ha.ne]
  conv_rhs => rw [← zero_add (b / (1 - a))]
  refine Tendsto.add ?_ tendsto_const_nhds
  conv_rhs => rw [← zero_mul (u 0 - (b / (1 - a)))]
  refine Tendsto.mul_const _ ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one ha_pos ha

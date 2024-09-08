/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clark Eggerman (original proof), Bjørn Kjos-Hanssen (use of ConvexOn.slope_mono)
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Basic

import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Convex.Deriv

/-!

In the paper 'Differentiating Convex Functions Constructively'
by Hannes Diener and Matthew Hendtlass, the increase in
'the approximate derivatives of f ' for convex functions
f : [0, 1] → ℝ is proved in Lemma 3. Here we formalize the proof.

Note that the proof provided in the paper does not account
for the case when y = x'. Because of this (and for effieciency)
the proof was changed, but we attempt to keep the spirit of the
proof.

Also note that the formalization uses `f : ℝ → ℝ` instead of
f : ↑(Set.Icc 0 1) → ℝ because the ConvexOn in Mathlib would
require that 'AddCommMonoid ↑(Set.Icc 0 1)'.

-/

/-- A rephrasing of `ConvexOn.slope_mono`. -/
lemma Neighbors {x y z : ℝ} {f : ℝ → ℝ} (Con : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hx : (x : ℝ) ∈ Set.Icc 0 1)(hz : (z : ℝ) ∈ Set.Icc 0 1) (ha1 : x < y)
    (ha2 : y < z) : slope f x y ≤ slope f y z := by
  rw [slope_comm]
  exact ConvexOn.slope_mono Con
    (show y ∈ Set.Icc 0 1 by simp_all only [Set.mem_Icc]; constructor <;> linarith)
    (show x ∈ Set.Icc 0 1 \ {y} by simp_all only [Set.mem_Icc, Set.mem_diff, and_self,
      Set.mem_singleton_iff, true_and]; linarith)
    (show z ∈ Set.Icc 0 1 \ {y} by simp_all only [Set.mem_Icc, Set.mem_diff, and_self,
      Set.mem_singleton_iff, true_and];linarith)
    (by linarith)

/-- 'Differentiating Convex Functions Constructively'
by Hannes Diener and Matthew Hendtlass, Lemma 3. -/
lemma Lemma_3 {x y x' y' : ℝ} (f : ℝ → ℝ) (Con : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hx : (x : ℝ) ∈ Set.Icc 0 1) (hy : (y : ℝ) ∈ Set.Icc 0 1)
    (hx' : (x' : ℝ) ∈ Set.Icc 0 1) (hy' : (y' : ℝ) ∈ Set.Icc 0 1)
    (ha1 : x < y) (ha2 : y ≤ x') (ha3 : x' < y') :
    slope f x y ≤ slope f x' y' := by
  have ha4 : y = x' ∨ y < x' := Decidable.eq_or_lt_of_le ha2
  cases ha4 with
  | inl equal =>
    subst y
    exact Neighbors Con hx hy' ha1 ha3
  | inr less_than =>
    exact le_of_not_gt (fun a => by
    cases (LT.lt.lt_or_lt a (slope f y x')) with
    | inl hl => exact not_le_of_gt hl <| Neighbors Con hy hy' less_than ha3
    | inr hr => exact not_le_of_gt hr <| Neighbors Con hx hx' ha1 less_than
    )

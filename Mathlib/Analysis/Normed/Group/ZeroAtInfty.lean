/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# ZeroAtInftyContinuousMapClass in normed additive groups

In this file we give a characterization of the predicate `zero_at_infty` from
`ZeroAtInftyContinuousMapClass`. A continuous map `f` is zero at infinity if and only if
for every `ε > 0` there exists a `r : ℝ` such that for all `x : E` with `r < ‖x‖` it holds that
`‖f x‖ < ε`.
-/

public section

open Topology Filter

variable {E F 𝓕 : Type*}
variable [SeminormedAddGroup E] [SeminormedAddCommGroup F]
variable [FunLike 𝓕 E F] [ZeroAtInftyContinuousMapClass 𝓕 E F]

theorem ZeroAtInftyContinuousMapClass.norm_le (f : 𝓕) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε := by
  have h := zero_at_infty f
  rw [tendsto_zero_iff_norm_tendsto_zero, tendsto_def] at h
  specialize h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rcases Metric.closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hr'
  suffices x ∈ (fun x ↦ ‖f x‖) ⁻¹' Metric.ball 0 ε by simp_all
  apply hr
  simp_all

variable [ProperSpace E]

theorem zero_at_infty_of_norm_le (f : E → F)
    (h : ∀ (ε : ℝ) (_hε : 0 < ε), ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε) :
    Tendsto f (cocompact E) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  intro s hs
  rw [mem_map, Metric.mem_cocompact_iff_closedBall_compl_subset 0]
  rw [Metric.mem_nhds_iff] at hs
  rcases hs with ⟨ε, hε, hs⟩
  rcases h ε hε with ⟨r, hr⟩
  use r
  intro
  aesop

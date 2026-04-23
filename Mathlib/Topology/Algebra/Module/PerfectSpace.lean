/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Map
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-! # Vector spaces over nontrivially normed fields are perfect spaces -/

@[expose] public section

open Filter Set
open scoped Topology

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Nontrivial E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]

include 𝕜 in
lemma perfectSpace_of_module : PerfectSpace E := by
  refine ⟨fun x hx ↦ ?_⟩
  let ⟨r, hr₀, hr⟩ := NormedField.exists_norm_lt_one 𝕜
  obtain ⟨c, hc⟩ : ∃ (c : E), c ≠ 0 := exists_ne 0
  have A : Tendsto (fun (n : ℕ) ↦ x + r ^ n • c) atTop (𝓝 (x + (0 : 𝕜) • c)) := by
    apply Tendsto.add tendsto_const_nhds
    exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).smul tendsto_const_nhds
  have B : Tendsto (fun (n : ℕ) ↦ x + r ^ n • c) atTop (𝓝[univ \ {x}] x) := by
    simp only [zero_smul, add_zero] at A
    simp [tendsto_nhdsWithin_iff, A, hc, norm_pos_iff.mp hr₀]
  exact accPt_principal_iff_nhdsWithin.mpr ((atTop_neBot.map _).mono B)

instance : PerfectSpace 𝕜 := perfectSpace_of_module 𝕜 𝕜

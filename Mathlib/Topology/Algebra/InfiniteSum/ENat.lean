/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Infinite sums in extended natural numbers

This file proves results on infinite sums in `ℕ∞`.
-/

public section

open Filter Topology
variable {α ι : Type*} {L : SummationFilter α}

namespace ENat

@[norm_cast]
protected theorem hasSum_coe {f : α → ℕ} {r : ℕ} :
    HasSum (fun a ↦ (f a : ℕ∞)) r L ↔ HasSum f r L := by
  simp_rw [HasSum, ← Nat.cast_sum]
  exact isOpenEmbedding_natCast.tendsto_nhds_iff.symm

protected theorem tsum_coe_eq [L.NeBot] {f : α → ℕ} {r : ℕ} (h : HasSum f r L) :
    ∑'[L] a, (f a : ℕ∞) = r :=
  (ENat.hasSum_coe.2 h).tsum_eq

protected theorem coe_tsum [L.NeBot] {f : α → ℕ} (hf : Summable f L) :
    ↑(∑'[L] a, f a) = ∑'[L] a, (f a : ℕ∞) := by
  rw [hf.hasSum.tsum_eq, ENat.tsum_coe_eq hf.hasSum]

end ENat

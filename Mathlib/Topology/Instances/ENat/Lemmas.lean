/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENat

/-!
# Some topology lemmas for `ℕ∞`
-/

variable {α : Type*} {f : α → ℕ∞}

lemma ENat.tsum_eq_top_of_infinite_support (h : (Function.support f).Infinite) :
    ∑' (i : α), f i = ⊤ := by
  rw [eq_top_iff, CompleteLinearOrder.tsum_eq_iSup]
  refine ENat.forall_natCast_le_iff_le.mp fun n _ ↦ ?_
  obtain ⟨t, ht, rfl⟩ := h.exists_subset_card_eq n
  refine le_trans ?_ (le_iSup _ t)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_le_sum fun i hi ↦ ENat.one_le_iff_ne_zero.mpr (ht hi)

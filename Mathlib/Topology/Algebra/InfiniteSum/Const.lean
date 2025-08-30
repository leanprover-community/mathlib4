/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sum/product of a constant function

This is in a separate file because it depends on `Nat.card` and hence cardinals.
-/

open Finset

@[to_additive (attr := simp)]
theorem tprod_const
    {β G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T2Space G] (a : G) :
    ∏' _ : β, a = a ^ (Nat.card β) := by
  rcases finite_or_infinite β with hβ|hβ
  · letI : Fintype β := Fintype.ofFinite β
    rw [tprod_eq_prod (s := univ) (fun x hx ↦ (hx (mem_univ x)).elim)]
    simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, pow_zero]
    rcases eq_or_ne a 1 with rfl | ha
    · simp
    · apply tprod_eq_one_of_not_multipliable
      simpa [multipliable_const_iff] using ha

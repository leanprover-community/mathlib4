/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/


variable {V : Type} (G : SimpleGraph V)

namespace SimpleGraph

instance [Finite V] : IsEmpty G.end where
  false := by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).nonempty
    exact Set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Finset.coe_univ, Set.mem_univ], h⟩

/-- The `componentCompl`s chosen by an end are all infinite. -/
lemma end_componentCompl_infinite (e : G.end) (K : (Finset V)ᵒᵖ) :
    ((e : (j : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj j) K).supp.Infinite := by
  refine (e.val K).infinite_iff_in_all_ranges.mpr (fun L h => ?_)
  change Opposite.unop K ⊆ Opposite.unop (Opposite.op L) at h
  exact ⟨e.val (Opposite.op L), (e.prop (CategoryTheory.opHomOfLE h))⟩

instance componentComplFunctor_nonempty_of_infinite [Infinite V] (K : (Finset V)ᵒᵖ) :
    Nonempty (G.componentComplFunctor.obj K) := G.componentCompl_nonempty_of_infinite K.unop

instance componentComplFunctor_finite [LocallyFinite G] [Fact G.Preconnected]
    (K : (Finset V)ᵒᵖ) : Finite (G.componentComplFunctor.obj K) := G.componentCompl_finite K.unop

/-- A locally finite preconnected infinite graph has at least one end. -/
lemma nonempty_ends_of_infinite [LocallyFinite G] [Fact G.Preconnected] [Infinite V] :
    G.end.Nonempty := by
  classical
  apply nonempty_sections_of_finite_inverse_system G.componentComplFunctor

end SimpleGraph

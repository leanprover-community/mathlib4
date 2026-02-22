/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Sigma-algebra on simple graphs

In this file, we pull back the sigma-algebra on `V → V → Prop` to a sigma-algebra on
`SimpleGraph V` and prove that common operations are measurable.
-/

public section

open MeasureTheory
open scoped Finset

namespace SimpleGraph
variable {V : Type*}

instance : MeasurableSpace (SimpleGraph V) := .comap Adj inferInstance

/-- A simple graph-valued map is measurable iff all induced adjacency maps are measurable. -/
lemma measurable_iff_adj {Ω : Type*} {m : MeasurableSpace Ω} {G : Ω → SimpleGraph V} :
    Measurable G ↔ ∀ u v, Measurable fun ω ↦ (G ω).Adj u v := by
  simp [measurable_comap_iff, measurable_pi_iff]

@[fun_prop]
lemma measurable_adj : Measurable (Adj : SimpleGraph V → V → V → Prop) := comap_measurable _

@[fun_prop]
lemma measurable_edgeSet : Measurable (edgeSet : SimpleGraph V → Set (Sym2 V)) :=
  measurable_set_iff.2 <| by rintro ⟨u, v⟩; simp only [mem_edgeSet]; fun_prop

@[simp, fun_prop]
lemma measurable_fromEdgeSet : Measurable (fromEdgeSet : Set (Sym2 V) → SimpleGraph V) := by
  simp only [measurable_iff_adj, fromEdgeSet_adj, ne_eq]; fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma measurableEmbedding_edgeSet [Countable V] :
    MeasurableEmbedding (edgeSet : SimpleGraph V → Set (Sym2 V)) where
  injective := edgeSet_injective
  measurable := measurable_edgeSet
  measurableSet_image' s hs := by
    simp only [← measurable_mem, Set.mem_image, edgeSet_eq_iff, ↓existsAndEq, true_and,
      Set.disjoint_right]
    refine .and (hs.mem.comp measurable_fromEdgeSet) <| .forall fun e ↦ .imp ?_ ?_ <;> fun_prop

end SimpleGraph

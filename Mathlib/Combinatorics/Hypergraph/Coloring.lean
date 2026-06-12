/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module
public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Coloring of a hypergraph

We define a coloring of a hypergraph to be a labeling of its edges such that adjacent edges are
labeled differently.

## Main definitions

* `Hypergraph.EdgeLabeling H K`: A labeling of the edges of a hypergraph `H` with labels in `K`.
* `Hypergraph.EdgeColoring H K`: A coloring of the edges of a hypergraph `H` with colors in `K`.
* `Hypergraph.chromaticIndex`: The smallest natural number `n` such that the edges of a hypergraph
  `H` can be colored with `n` colors.
-/

public section

variable {α : Type*} (H : Hypergraph α) (K K' : Type*)

namespace Hypergraph

/-- An edge-labeling of a hypergraph `H` with labels in type `K`. Sometimes this is called an
edge-coloring, but we reserve that terminology for labelings where adjacent edges are labeled
differently. -/
structure EdgeLabeling where
  /-- The assignment from edges of `H` to labels in `K`. -/
  labeling : H.edgeSet → K

/-- An edge-coloring of a hypergraph `H` with labels in type `K` is an edge-labeling where adjacent
edges are labeled differently. -/
structure EdgeColoring extends EdgeLabeling H K where
  isValid : ∀ e e' : H.edgeSet, H.EAdj e e' → labeling e = labeling e' → e = e'

/-- The "tautological" edge-coloring of a hypergraph, using the edges of the graph as colors. -/
def selfEdgeColoring : H.EdgeColoring H.edgeSet where
  labeling := id
  isValid := by simp

/-- A hypergraph with no edges can be edge-colored with no colors. -/
def IsTrivial.edgeColoring (h : H.IsTrivial) : EdgeColoring H Empty where
  labeling e := (h.not_mem_edgeSet e.2).elim
  isValid := by simp [h.not_mem_edgeSet]

variable {H K K'}

/-- Compose an edge-labeling of a hypergraph with a function on the type of colors. -/
def EdgeLabeling.compRight (c : H.EdgeLabeling K) (f : K → K') : H.EdgeLabeling K' where
  labeling := f ∘ c.labeling

@[simp]
theorem EdgeLabeling.compRight_labeling (c : H.EdgeLabeling K) (f : K → K') :
    (c.compRight f).labeling = f ∘ c.labeling := by
  rfl

/-- Compose an edge-labeling of a hypergraph with an injective function on the type of colors. -/
def EdgeColoring.compRight (c : H.EdgeColoring K) {f : K → K'} (hf : f.Injective) :
    H.EdgeColoring K' where
  __ := c.toEdgeLabeling.compRight f
  isValid := by simpa [hf.eq_iff] using c.isValid

@[simp]
theorem EdgeColoring.compRight_labeling (c : H.EdgeColoring K) {f : K → K'} (hf : f.Injective) :
    (c.compRight hf).labeling = f ∘ c.labeling :=
  c.toEdgeLabeling.compRight_labeling f

variable (H) in
/-- The chromatic index of a hypergraph `H` is the smallest natural number `n` such that the edges
of `H` can be colored with `n` colors. -/
noncomputable def chromaticIndex : ℕ :=
  sInf {n : ℕ | Nonempty (H.EdgeColoring (Fin n))}

/-- Any edge-coloring of a hypergraph gives an upper bound on the chromatic index. -/
theorem EdgeColoring.chromaticIndex_le (c : H.EdgeColoring K) [Finite K] :
    H.chromaticIndex ≤ Nat.card K :=
  Nat.sInf_le ⟨c.compRight (Finite.equivFin K).injective⟩

/-- A hypergraph with no edges has chromatic index zero. -/
theorem IsTrivial.chromaticIndex_eq_zero (h : H.IsTrivial) : H.chromaticIndex = 0 := by
   simpa using h.edgeColoring.chromaticIndex_le

end Hypergraph

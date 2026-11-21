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

end Hypergraph

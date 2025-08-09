/-
Copyright (c) 2025 Sebastian Kumar, Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar, Xiangyu Li
-/
import Mathlib.Data.Finset.Image

/-!
# Simplicial complexes

This file introduces finite (abstract) simplicial complexes in a purely combinatorial form.

A simplicial complex on a vertex type `V` is a downward-closed set of finite subsets of `V`
(its *faces*).

Only the basic structure and elementary remarks appear here. Morphisms, categorical bundling,
and geometric realisation are handled in later files.

## Main definitions

* `SimplicialComplex V` :
  a structure with `faces : Set (Finset V)` which is closed under taking subsets.
* `Face X` :
  the subtype of faces of a given complex `X` (i.e. `Finset V` equipped with the proof
  that it lies in `X.faces`).

## Implementation notes

* We do not assume that the empty face belongs to `faces`; if a later development
  requires this, it should be added as an extra hypothesis.
* We do not require singletons to be a face.

## References

* <https://en.wikipedia.org/wiki/Simplicial_complex>

## Tags

simplicial complex, combinatorial topology
-/

open Function

universe u

/-- A simplicial complex on a vertex type `V` is a downward‑closed family
of finite vertex sets (faces). -/
@[ext] structure SimplicialComplex (V : Type u) where
  /-- The collection of faces (finite vertex sets). -/
  faces : Set (Finset V)
  /-- Downward closure: every subset of a face is again a face. -/
  downward_closed :
    ∀ ⦃s t : Finset V⦄, s ∈ faces → t ⊆ s → t ∈ faces

namespace SimplicialComplex

variable {V : Type u}

/-- A face of `X` (as a subtype). -/
abbrev Face (X : SimplicialComplex V) := {A : Finset V // A ∈ X.faces}

end SimplicialComplex

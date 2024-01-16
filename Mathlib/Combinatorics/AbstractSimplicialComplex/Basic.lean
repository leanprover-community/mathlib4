/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel

Adapted from the Lean3 file of Shing Tak Lam.
-/
import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PartENat

/-!
# Abstract Simplicial Complex

In this file, we define abstract simplicial complexes over a vertex set `V`. An abstract simplicial
complex is a collection of (nonempty) simplices which is closed by inclusion (of vertices).

We model them as downwards-closed collections of nonempty finite subsets of `V` such that every singleton
of 'V' is a face. We also give a function constructing on abstract simplicial complex from an
abstract simplicial complex on a type α, defined as a downwards-closed collection of nonempty
finite subsets of α.


/- Rewrite the next part.-/
## Main definitions

* `AbstractSimplicialComplex V`: An abstract simplicial complex with vertices in `V`.
* `AbstractSimplicialComplex.vertices`: The zero dimensional faces of a simplicial complex.
* `AbstractSimplicialComplex.facets`: The maximal faces of a simplicial complex.
* `SimplicialMap K L`: Simplicial maps from a simplicial complex `K` to another
  simplicial complex `L`.

## Notation

* `s ∈ K` means `s` is a face of `K`.
* `K ≤ L` means that `K` is a subcomplex of `L`. That is, all faces of `K` are faces of `L`.
* `K →ₛ L` is a `simplicial_map K L`.

## TODO (maybe)

* `geometry.simplicial_complex` can `extend AbstractSimplicialComplex`.
* Define the geometric realisation of an abstract simplicial complex.

-/

set_option autoImplicit false


universe u v w

@[ext]
structure AbstractSimplicialComplex (V : Type u) :=
(faces : Set (Finset V))
(nonempty_of_mem : ∀ {s : Finset V}, s ∈ faces → s.Nonempty)
(down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)
(vertices : ∀ {a : V}, {a} ∈ faces)


@[ext]
structure AbstractSimplicialComplexOn (α : Type u) :=
(faces : Set (Finset α))
(nonempty_of_mem : ∀ {s : Finset α}, s ∈ faces → s.Nonempty)
(down_closed : ∀ {s t : Finset α}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)

/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Sets.Closeds

/-!
# The Krull dimension of a topological space

The Krull dimension of a topological space is the order theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.

TODO: The Krull dimension of `Spec(R)` equals the Krull dimension of `R`, for `R` a commutative
  ring.
-/

open TopologicalSpace

/--
The Krull dimension of a topological space is the supremum of lengths of chains of
closed irreducible sets.
-/
noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
  Order.krullDim (IrreducibleCloseds T)

/-
Map induced on irreducible closed susets by a closed continuous map f.
This is just a wrapper around the image of f together with proofs that it
preserves irreducibility (by continuity) and closedness (since f is closed).
-/
def inducedMapOnIrreducibleCloseds {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (cont : Continuous f) (closed : IsClosedMap f) :
    IrreducibleCloseds X → IrreducibleCloseds Y := fun u ↦ {
      carrier := f '' u
      is_irreducible' := by
        exact IsIrreducible.image u.is_irreducible' f (Continuous.continuousOn cont)
      is_closed' := by exact closed u u.is_closed'
    }

/-
The image of an injective closed continuous map is strictly monotone on the preorder
of irreducible closeds.
-/
lemma inducedMapOnIrreducibleCloseds_strictMono {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (cont : Continuous f) (closed : IsClosedMap f) (inj : Function.Injective f) :
    StrictMono (inducedMapOnIrreducibleCloseds cont closed) := by
  intro U V UltV
  exact Function.Injective.image_strictMono inj UltV

/-
If f : X → Y is a continuous closed injection, then the Krull dimension of X is less than or equal
to the Krull dimension of Y.
-/
theorem topologicalKrullDim_le_of_closed_injection {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (cont : Continuous f)
    (closed : IsClosedMap f) (inj : Function.Injective f) :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  exact Order.krullDim_le_of_strictMono
   (inducedMapOnIrreducibleCloseds cont closed)
   (inducedMapOnIrreducibleCloseds_strictMono cont closed inj)

/-
The topological Krull dimension is invariant under homeomorphisms
-/
theorem topologicalKrullDim_eq_of_homeo (X Y : Type*)
 [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
 (h : IsHomeomorph f) : topologicalKrullDim X = topologicalKrullDim Y :=

  let fwd : topologicalKrullDim X ≤ topologicalKrullDim Y :=
   topologicalKrullDim_le_of_closed_injection f h.continuous
    (IsHomeomorph.isClosedMap h) h.bijective.injective

  let bwd : topologicalKrullDim Y ≤ topologicalKrullDim X :=
   topologicalKrullDim_le_of_closed_injection (h.homeomorph f).symm (Homeomorph.continuous_symm
    (IsHomeomorph.homeomorph f h))
    (Homeomorph.isClosedMap (IsHomeomorph.homeomorph f h).symm) (Homeomorph.injective
      (IsHomeomorph.homeomorph f h).symm)

  le_antisymm fwd bwd

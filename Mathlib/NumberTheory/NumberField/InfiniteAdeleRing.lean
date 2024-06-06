/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.NumberField.Embeddings

/-!
# Infinite adele ring of a number field

This file formalises the definition of the infinite adele ring of a number field `K` as the
product of completions of `K` over its infinite places and we show that it is locally compact.
Completions `v.completion` of a number field at an infinite place `v` are formalised in
`Mathlib.NumberTheory.NumberField.Embeddings`.

## Main definitions
* `NumberField.infiniteAdeleRing K` of a number field `K` is defined as the product of
the completions of `K` over its Archimedean places.
* `NumberField.InfiniteAdeleRing.globalEmbedding K` is the embedding from `K` to
`infiniteAdeleRing K` sending `x` to `(x)ᵥ`.

## Main results
* `NumberField.InfiniteAdeleRing.locallyCompactSpace K` : the infinite adele ring of `K` is a
locally compact space.

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
def infiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (infiniteAdeleRing K) := Pi.commRing

instance : Inhabited (infiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (infiniteAdeleRing K) := Pi.nontrivial

end DerivedInstances

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K) := Pi.topologicalSpace

instance topologicalRing : TopologicalRing (infiniteAdeleRing K) := Pi.instTopologicalRing

/-- The global embedding of a number field into its infinite adele ring,
sending `x ∈ K` to `(x)ᵥ`. -/
def globalEmbedding : K →+* infiniteAdeleRing K :=
  Pi.ringHom (fun (v : InfinitePlace K) => InfinitePlace.Completion.coeRingHom v)

theorem globalEmbedding_injective : Function.Injective (globalEmbedding K) :=
  (globalEmbedding K).injective

/-- The infinite adele ring is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

end InfiniteAdeleRing

end NumberField

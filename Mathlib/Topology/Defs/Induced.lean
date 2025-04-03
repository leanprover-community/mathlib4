/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Topology.Basic
/-!
# Induced and coinduced topologies

In this file we define the induced and coinduced topologies,
as well as topology inducing maps, topological embeddings, and quotient maps.

## Main definitions

* `TopologicalSpace.induced`: given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous.

* `TopologicalSpace.coinduced`: given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous.

* `Inducing`: a map `f : X → Y` is called *inducing*,
  if the topology on the domain is equal to the induced topology.

* `Embedding`: a map `f : X → Y` is an *embedding*,
  if it is a topology inducing map and it is injective.

* `OpenEmbedding`: a map `f : X → Y` is an *open embedding*,
  if it is an embedding and its range is open.
  An open embedding is an open map.

* `ClosedEmbedding`: a map `f : X → Y` is an *open embedding*,
  if it is an embedding and its range is open.
  An open embedding is an open map.

* `QuotientMap`: a map `f : X → Y` is a *quotient map*,
  if it is surjective
  and the topology on the codomain is equal to the coinduced topology.
-/

open Set

namespace TopologicalSpace

variable {X Y : Type*}

/-- Given `f : X → Y` and a topology on `Y`,
  the induced topology on `X` is the collection of sets
  that are preimages of some open set in `Y`.
  This is the coarsest topology that makes `f` continuous. -/
def induced (f : X → Y) (t : TopologicalSpace Y) : TopologicalSpace X where
  IsOpen s := ∃ t, IsOpen t ∧ f ⁻¹' t = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩
    exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion S h := by
    choose! g hgo hfg using h
    refine ⟨⋃₀ (g '' S), isOpen_sUnion <| forall_mem_image.2 hgo, ?_⟩
    rw [preimage_sUnion, biUnion_image, sUnion_eq_biUnion]
    exact iUnion₂_congr hfg
#align topological_space.induced TopologicalSpace.induced

/-- Given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous. -/
def coinduced (f : X → Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter s₁ s₂ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h
#align topological_space.coinduced TopologicalSpace.coinduced

end TopologicalSpace

variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- A function `f : X → Y` between topological spaces is inducing if the topology on `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff it is the preimage
under `f` of some open set `t : Set Y`. -/
@[mk_iff]
structure Inducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  induced : tX = tY.induced f
#align inducing Inducing
#align inducing_iff inducing_iff

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set. -/
@[mk_iff]
structure Embedding [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) extends
  Inducing f : Prop where
  /-- A topological embedding is injective. -/
  inj : Function.Injective f
#align embedding Embedding
#align embedding_iff embedding_iff

/-- An open embedding is an embedding with open range. -/
@[mk_iff]
structure OpenEmbedding (f : X → Y) extends Embedding f : Prop where
  /-- The range of an open embedding is an open set. -/
  isOpen_range : IsOpen <| range f
#align open_embedding OpenEmbedding
#align open_embedding_iff openEmbedding_iff

/-- A closed embedding is an embedding with closed image. -/
@[mk_iff]
structure ClosedEmbedding (f : X → Y) extends Embedding f : Prop where
  /-- The range of a closed embedding is a closed set. -/
  isClosed_range : IsClosed <| range f
#align closed_embedding ClosedEmbedding
#align closed_embedding_iff closedEmbedding_iff

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : Set Y`, `s` is open iff its preimage is an open set. -/
def QuotientMap {X : Type*} {Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) : Prop :=
  Function.Surjective f ∧ tY = tX.coinduced f
#align quotient_map QuotientMap

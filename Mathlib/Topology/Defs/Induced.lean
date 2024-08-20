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

* `IsInducing`: a map `f : X → Y` is called *inducing*,
  if the topology on the domain is equal to the induced topology.

* `Embedding`: a map `f : X → Y` is an *embedding*,
  if it is a topology inducing map and it is injective.

* `IsOpenEmbedding`: a map `f : X → Y` is an *open embedding*,
  if it is an embedding and its range is open.
  An open embedding is an open map.

* `IsClosedEmbedding`: a map `f : X → Y` is an *open embedding*,
  if it is an embedding and its range is open.
  An open embedding is an open map.

* `IsQuotientMap`: a map `f : X → Y` is a *quotient map*,
  if it is surjective
  and the topology on the codomain is equal to the coinduced topology.
-/

open Set
open scoped Topology

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

instance _root_.instTopologicalSpaceSubtype {p : X → Prop} [t : TopologicalSpace X] :
    TopologicalSpace (Subtype p) :=
  induced (↑) t

/-- Given `f : X → Y` and a topology on `X`,
  the coinduced topology on `Y` is defined such that
  `s : Set Y` is open if the preimage of `s` is open.
  This is the finest topology that makes `f` continuous. -/
def coinduced (f : X → Y) (t : TopologicalSpace X) : TopologicalSpace Y where
  IsOpen s := IsOpen (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h

end TopologicalSpace

namespace Topology
variable {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- We say that restrictions of the topology on `X` to sets from a family `S`
generates the original topology,
if either of the following equivalent conditions hold:

- a set which is relatively open in each `s ∈ S` is open;
- a set which is relatively closed in each `s ∈ S` is closed;
- for any topological space `Y`, a function `f : X → Y` is continuous
  provided that it is continuous on each `s ∈ S`.
-/
structure IsRestrictGen (S : Set (Set X)) : Prop where
  isOpen_of_forall_induced (u : Set X) : (∀ s ∈ S, IsOpen ((↑) ⁻¹' u : Set s)) → IsOpen u

/-- A function `f : X → Y` between topological spaces is inducing if the topology on `X` is induced
by the topology on `Y` through `f`, meaning that a set `s : Set X` is open iff it is the preimage
under `f` of some open set `t : Set Y`. -/
@[mk_iff]
structure IsInducing (f : X → Y) : Prop where
  /-- The topology on the domain is equal to the induced topology. -/
  eq_induced : tX = tY.induced f

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : Set X`, `s` is open iff it is the preimage of an open set. -/
@[mk_iff]
structure IsEmbedding (f : X → Y) extends IsInducing f : Prop where
  /-- A topological embedding is injective. -/
  inj : Function.Injective f

/-- An open embedding is an embedding with open range. -/
@[mk_iff]
structure IsOpenEmbedding (f : X → Y) extends IsEmbedding f : Prop where
  /-- The range of an open embedding is an open set. -/
  isOpen_range : IsOpen <| range f

@[deprecated (since := "2024-10-18")]
alias OpenEmbedding := IsOpenEmbedding

/-- A closed embedding is an embedding with closed image. -/
@[mk_iff]
structure IsClosedEmbedding (f : X → Y) extends IsEmbedding f : Prop where
  /-- The range of a closed embedding is a closed set. -/
  isClosed_range : IsClosed <| range f

@[deprecated (since := "2024-10-20")]
alias ClosedEmbedding := IsClosedEmbedding

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : Set Y`, `s` is open iff its preimage is an open set. -/
@[mk_iff quotientMap_iff']
structure IsQuotientMap {X : Type*} {Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) : Prop where
  surjective : Function.Surjective f
  eq_coinduced : tY = tX.coinduced f

end Topology

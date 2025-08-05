/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.CompactOpen

/-!
# Equivalence between `C(X, Σ i, Y i)` and `Σ i, C(X, Y i)`

If `X` is a connected topological space, then for every continuous map `f` from `X` to the disjoint
union of a collection of topological spaces `Y i` there exists a unique index `i` and a continuous
map from `g` to `Y i` such that `f` is the composition of the natural embedding
`Sigma.mk i : Y i → Σ i, Y i` with `g`.

This defines an equivalence between `C(X, Σ i, Y i)` and `Σ i, C(X, Y i)`. In fact, this equivalence
is a homeomorphism if the spaces of continuous maps are equipped with the compact-open topology.

## Implementation notes

There are two natural ways to talk about this result: one is to say that for each `f` there exist
unique `i` and `g`; another one is to define a noncomputable equivalence. We choose the second way
because it is easier to use an equivalence in applications.

## TODO

Some results in this file can be generalized to the case when `X` is a preconnected space. However,
if `X` is empty, then any index `i` will work, so there is no 1-to-1 correspondence.

## Keywords

continuous map, sigma type, disjoint union
-/

noncomputable section

open Filter Topology

variable {X ι : Type*} {Y : ι → Type*} [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]

namespace ContinuousMap

theorem isEmbedding_sigmaMk_comp [Nonempty X] :
    IsEmbedding (fun g : Σ i, C(X, Y i) ↦ (sigmaMk g.1).comp g.2) where
  toIsInducing := inducing_sigma.2
    ⟨fun i ↦ (sigmaMk i).isInducing_postcomp IsEmbedding.sigmaMk.isInducing, fun i ↦
      let ⟨x⟩ := ‹Nonempty X›
      ⟨_, (isOpen_sigma_fst_preimage {i}).preimage (continuous_eval_const x), fun _ ↦ Iff.rfl⟩⟩
  injective := by
    rintro ⟨i, g⟩ ⟨i', g'⟩ h
    obtain ⟨rfl, hg⟩ : i = i' ∧ ⇑g ≍ ⇑g' :=
      Function.eq_of_sigmaMk_comp <| congr_arg DFunLike.coe h
    simpa using hg

section ConnectedSpace

variable [ConnectedSpace X]

/-- Every continuous map from a connected topological space to the disjoint union of a family of
topological spaces is a composition of the embedding `ContinuousMap.sigmaMk i : C(Y i, Σ i, Y i)`
for some `i` and a continuous map `g : C(X, Y i)`. See also `Continuous.exists_lift_sigma` for a
version with unbundled functions and `ContinuousMap.sigmaCodHomeomorph` for a homeomorphism defined
using this fact. -/
theorem exists_lift_sigma (f : C(X, Σ i, Y i)) : ∃ i g, f = (sigmaMk i).comp g :=
  let ⟨i, g, hg, hfg⟩ := (map_continuous f).exists_lift_sigma
  ⟨i, ⟨g, hg⟩, DFunLike.ext' hfg⟩

variable (X Y)

/-- Homeomorphism between the type `C(X, Σ i, Y i)` of continuous maps from a connected topological
space to the disjoint union of a family of topological spaces and the disjoint union of the types of
continuous maps `C(X, Y i)`.

The inverse map sends `⟨i, g⟩` to `ContinuousMap.comp (ContinuousMap.sigmaMk i) g`. -/
@[simps! symm_apply]
def sigmaCodHomeomorph : C(X, Σ i, Y i) ≃ₜ Σ i, C(X, Y i) :=
  .symm <| Equiv.toHomeomorphOfIsInducing
    (.ofBijective _ ⟨isEmbedding_sigmaMk_comp.injective, fun f ↦
      let ⟨i, g, hg⟩ := f.exists_lift_sigma; ⟨⟨i, g⟩, hg.symm⟩⟩)
    isEmbedding_sigmaMk_comp.isInducing

end ConnectedSpace

end ContinuousMap

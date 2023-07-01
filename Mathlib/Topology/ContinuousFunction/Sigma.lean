/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Connected
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
if `X` is empty, then any index `i` will work, so there is no 1-to-1 corespondence.

## Keywords

continuous map, sigma type, disjoint union
-/

noncomputable section

variable {X ι : Type _} {Y : ι → Type _} [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
  [ConnectedSpace X]

theorem ContinuousMap.exists_lift_sigma (f : C(X, Σ i, Y i)) :
    ∃ (i : ι) (g : C(X, Y i)), f = (sigmaMk i).comp g :=
  let ⟨i, g, hg, hfg⟩ := f.continuous.exists_lift_sigma
  ⟨i, ⟨g, hg⟩, FunLike.ext' hfg⟩

variable (X Y)

/-- Equivalence between the type `C(X, Σ i, Y i)` of continuous maps from a connected topological
space to the disjoint union of a family of topological spaces and the disjoint union of the types of
continuous maps `C(X, Y i)`.

The inverse map sends `⟨i, g⟩` to `ContinuousMap.comp (ContinuousMap.sigmaMk i) g`. -/
@[simps! symm_apply]
def ContinuousMap.sigmaCodEquiv : C(X, Σ i, Y i) ≃ Σ i, C(X, Y i) :=
  .symm <| .ofBijective (fun g ↦ (sigmaMk g.1).comp g.2) <| by
    refine ⟨?_, fun f ↦ ?_⟩
    · rintro ⟨i, g⟩ ⟨i', g'⟩ h
      obtain ⟨rfl, hg⟩ : i = i' ∧ HEq (⇑g) (⇑g') :=
        Function.eq_of_sigmaMk_comp <| congr_arg FunLike.coe h
      simpa using hg
    · rcases f.exists_lift_sigma with ⟨i, g, rfl⟩
      exact ⟨⟨i, g⟩, rfl⟩



/-- A continuous map from a connected space to a `Σ`-type can be lifted to one of the
components `π i`. -/
theorem continuous_map.exists_lift_sigma {X ι : Type*} {π : ι → Type*} [topological_space X]
  [connected_space X] [∀ i, topological_space (π i)] (f : C(X, Σ i, π i)) :
  ∃ (i : ι) (g : C(X, π i)), f = continuous_map.comp ⟨sigma.mk i⟩ g :=
let ⟨i, g, hgc, hfg⟩ := f.continuous.exists_lift_sigma in
⟨i, ⟨g, hgc⟩, fun_like.ext' hfg⟩

noncomputable def equiv.continuous_map_sigma_equiv {X ι : Type*} {π : ι → Type*}
  [topological_space X] [connected_space X] [∀ i, topological_space (π i)] :
  C(X, Σ i, π i) ≃ Σ i, C(X, π i) :=
equiv.symm $ equiv.of_bijective (λ g, continuous_map.comp ⟨sigma.mk g.1⟩ g.2) $
  begin
    refine ⟨_, λ f, let ⟨i, g, h⟩ := f.exists_lift_sigma in ⟨⟨i, g⟩, h.symm⟩⟩,
    rintro ⟨i, g⟩ ⟨j, g'⟩ h,
    obtain ⟨rfl : i = j, h⟩ := function.eq_of_sigma_mk_comp (fun_like.ext'_iff.1 h),
    simpa using h
  end

/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang, Edison Xie
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!

# Continuous cohomology

We define continuous cohomology as the homology of the homogeneous cochain complex.

## Implementation details

We define homogeneous cochains as `g`-invariant continuous function in `C(G, C(G,...,C(G, M)))`
instead of the usual `C(Gⁿ, M)` to allow more general topological groups other than locally compact
ones. For this to work, we also work in `TopRep k G`, where the `G` action on `M`
is only continuous on `M`, and not necessarily continuous in both variables, because the `G` action
on `C(G, M)` might not be continuous on both variables even if it is on `M`.

For the differential map, instead of a finite sum we use the inductive definition
`d₋₁ : M → C(G, M) := const : m ↦ g ↦ m` and
`dₙ₊₁ : C(G, _) → C(G, C(G, _)) := const - C(G, dₙ) : f ↦ g ↦ f - dₙ (f (g))`
See `TopRep.d`.

## Main definition
- `TopRep.homogeneousCochains`:
  The functor taking an `R`-linear `G`-representation to the complex of homogeneous cochains.
- `continuousCohomology`:
  The functor taking an `R`-linear `G`-representation to its `n`-th continuous cohomology.

## TODO
- Show that it coincides with `groupCohomology` for discrete groups.
- Give the usual description of cochains in terms of `n`-ary functions for locally compact groups.
- Show that short exact sequences induce long exact sequences in certain scenarios.
-/

@[expose] public section

variable {k G : Type*} [Ring k] [Group G] [TopologicalSpace k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]

open CategoryTheory ContRepresentation Limits

namespace TopRep

/-- The `n`-th term in the resolution of a topological representation induced by `TopRep.coind₁`. -/
abbrev resolutionX (X : TopRep k G) : ℕ → TopRep k G
  | 0 => X
  | n + 1 => (resolutionX X n).coind₁

/-- The boundary map in the resolution of a topological representation induced
by `TopRep.coind₁Functor`. -/
def d (X : TopRep k G) : (n : ℕ) → resolutionX X n ⟶ resolutionX X (n + 1)
  | 0 => ofHom X.ρ.coind₁ι
  | n + 1 => ofHom (resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n)

lemma d_zero (X : TopRep k G) : d X 0 = ofHom X.ρ.coind₁ι := rfl

lemma d_succ (X : TopRep k G) (n : ℕ) :
    d X (n + 1) = ofHom (resolutionX X (n + 1)).ρ.coind₁ι - (coind₁Functor k G).map (d X n) :=
  rfl

lemma hom_d_succ (X : TopRep k G) (n : ℕ) :
    (d X (n + 1)).hom = (resolutionX X (n + 1)).ρ.coind₁ι -
      ContRepresentation.coind₁Map _ _ (d X n).hom :=
  rfl

@[reassoc (attr := simp)]
lemma d_comp_d (X : TopRep k G) (n : ℕ) : d X n ≫ d X (n + 1) = 0 := by
  induction n with
  | zero =>
    ext
    simp [d_succ, ContIntertwiningMap.toContinuousLinearMap_apply, d_zero, hom_sub]
  | succ n ih =>
    rw [d_succ _ (n + 1), Preadditive.comp_sub]
    nth_rw 2 [d_succ]
    rw [Preadditive.sub_comp, ← Functor.map_comp, ih, Functor.map_zero, sub_zero, sub_eq_zero]
    rfl

/-- The complex of functors whose behaviour pointwise takes an `R`-linear `G`-representation `M`
to the complex `M → C(G, M) → ⋯ → C(G, C(G,...,C(G, M))) → ⋯`
The `G`-invariant submodules of it is the homogeneous cochains (shifted by one). -/
abbrev resolution (X : TopRep k G) : CochainComplex (TopRep k G) ℕ :=
  CochainComplex.of (resolutionX X) (d X) (d_comp_d X)

/-- The shifted boundary map of the resolution. -/
def resolution'd (X : TopRep k G) (n : ℕ) :
    resolutionX X (n + 1) ⟶ resolutionX X (n + 1 + 1) := d X (n + 1)

lemma resolution'd₀_eq (X : TopRep k G) : resolution'd X 0 = d X 1 := rfl

/-- The shifted resolution of a topological representation by `1` degree. -/
abbrev resolution' (X : TopRep k G) : CochainComplex (TopRep k G) ℕ :=
  CochainComplex.of (fun i ↦ (resolution X).X (i + 1))
    (resolution'd X) (fun n ↦ d_comp_d X (n + 1))

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The homogeneous cochains of a topological representation. -/
abbrev homogeneousCochains (X : TopRep k G) :
    CochainComplex (TopModuleCat k) ℕ :=
  ((invariantsFunctor k G).mapHomologicalComplex _).obj (resolution' X)

lemma homogeneousCochains.d₀₁_eq (X : TopRep k G) :
    (homogeneousCochains X).d 0 1 = (invariantsFunctor k G).map (d X 1) := by
  rw [← resolution'd₀_eq]; rfl

lemma homogeneousCochains.d₀₁_apply (X : TopRep k G) (σ : (homogeneousCochains X).X 0) :
    ((homogeneousCochains X).d 0 1).hom σ = (d X 1).hom σ := rfl

/-- The continuous cohomology of a continuous representation defined
by `continuousCohomologyFunctor`. -/
noncomputable abbrev _root_.continuousCohomology (n : ℕ) (A : TopRep k G) :
    TopModuleCat k := (homogeneousCochains A).homology n

end TopRep

namespace ContinuousCohomology

open TopRep

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of homogeneous cochains. -/
noncomputable abbrev cocycles (A : TopRep k G) (n : ℕ) :
    TopModuleCat k := (homogeneousCochains A).cycles n

/-- The natural map from `n`-cocycles to `n`th continuous cohomology for a `k`-linear
`G`-representation `A`. -/
noncomputable abbrev π (A : TopRep k G) (n : ℕ) := (homogeneousCochains A).homologyπ n

end ContinuousCohomology

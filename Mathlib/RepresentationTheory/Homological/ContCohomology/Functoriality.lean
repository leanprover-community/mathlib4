/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Functoriality of continuous cohomology

Given topological groups `G` and `H`, a continuous group homomorphism `φ : H →ₜ* G`, a topological
representation `X` of `G`, a topological representation `Y` of `H`, and a morphism of topological
`H`-representations `f : res φ X ⟶ Y`, we construct a cochain map
`homogeneousCochains X ⟶ homogeneousCochains Y` and hence maps on continuous cohomology
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`.

## Main definitions

* `ContinuousCohomology.cochainsMap φ f` : the cochain map
  `homogeneousCochains X ⟶ homogeneousCochains Y` induced by `φ : H →ₜ* G` and
  `f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`.
* `ContinuousCohomology.map φ f n` : the induced map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous
  cohomology.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ContinuousCohomology

open TopRep ContRepresentation

variable {k : Type u} {G H K : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {X : TopRep k G} {Y : TopRep k H} {Z : TopRep k K}

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
def resolutionMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    (i : ℕ) → res φ (resolutionX X i) ⟶ resolutionX Y i
  | 0 => f
  | i + 1 => ofHom (coind₁ResMap φ (resolutionMap φ f i).hom)

@[simp]
lemma resolutionMap_zero (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    resolutionMap φ f 0 = f := rfl

lemma resolutionMap_succ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ f (i + 1) = ofHom (coind₁ResMap φ (resolutionMap φ f i).hom) := rfl

@[simp]
lemma resolutionMap_id (X : TopRep k G) (i : ℕ) :
    resolutionMap (ContinuousMonoidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, ih]
    ext F x
    rfl

lemma resolutionMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (i : ℕ) :
    resolutionMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) i =
      (resFunctor (ψ : K →* H)).map (resolutionMap φ f i) ≫ resolutionMap ψ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- The maps `resolutionMap φ f` commute with the differentials of the resolutions. -/
lemma resolutionMap_comp_d (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ f i ≫ d Y i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionMap φ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The cochain map `homogeneousCochains X ⟶ homogeneousCochains Y` induced by a continuous
group homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`. -/
@[simps! -isSimp f f_hom]
def cochainsMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    homogeneousCochains X ⟶ homogeneousCochains Y where
  f i := invariantsResMap φ (resolutionMap φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq, homogeneousCochains.d_eq, ← invariantsResMap_comp,
      resolutionMap_comp_d, invariantsResMap_map_comp]

@[simp]
lemma cochainsMap_id (X : TopRep k G) :
    cochainsMap (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X) := by
  ext i : 1
  rw [cochainsMap_f, resolutionMap_id]
  ext v
  rfl

@[reassoc]
lemma cochainsMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) :
    cochainsMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) =
      cochainsMap φ f ≫ cochainsMap ψ g := by
  ext i v x
  exact congr($(resolutionMap_comp φ ψ f g (i + 1)).hom v.1 x)

/-- The map `Zⁿ(G, X) ⟶ Zⁿ(H, Y)` on cocycles induced by a continuous group homomorphism
`φ : H →ₜ* G` and a morphism of topological `H`-representations `f : res φ X ⟶ Y`. -/
noncomputable abbrev cocyclesMap (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    cocycles X n ⟶ cocycles Y n :=
  HomologicalComplex.cyclesMap (cochainsMap φ f) n

@[simp]
lemma cocyclesMap_id (X : TopRep k G) (n : ℕ) :
    cocyclesMap (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [cocyclesMap]

@[reassoc]
lemma cocyclesMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (n : ℕ) :
    cocyclesMap (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n =
      cocyclesMap φ f n ≫ cocyclesMap ψ g n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

/-- The map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous cohomology induced by a continuous group
homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`. -/
noncomputable abbrev map (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  HomologicalComplex.homologyMap (cochainsMap φ f) n

@[reassoc]
theorem π_map (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    π X n ≫ map φ f n = cocyclesMap φ f n ≫ π Y n := by
  simp [map, cocyclesMap]

@[simp]
lemma map_id (X : TopRep k G) (n : ℕ) :
    map (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [map]

@[reassoc]
lemma map_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : ℕ) :
    map (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n = map φ f n ≫ map ψ g n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

end ContinuousCohomology

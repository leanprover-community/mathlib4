/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# The category of `C^n` manifolds modeled on `I`

`ModelWithCorners.MfldCat.{u} I n` is the category of bundled `C^n` manifolds modeled on a *fixed*
`I : ModelWithCorners 𝕜 E H`.

## Future work
* Show that `ModelWithCorners.MfldCat I n` has coproducts given by disjoint unions.
-/

@[expose] public section

open CategoryTheory
open scoped Manifold ContDiff

universe u v

namespace ModelWithCorners

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

set_option backward.privateInPublic true in
/-- The category of `C^n` manifolds modeled on a fixed model with corners `I`. -/
structure MfldCat (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace H carrier]
  [isManifold : IsManifold I n carrier]

attribute [instance] MfldCat.topologicalSpace MfldCat.chartedSpace MfldCat.isManifold

initialize_simps_projections MfldCat (-topologicalSpace, -chartedSpace, -isManifold)

namespace MfldCat
variable {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I n Z]

instance : CoeSort (MfldCat I n) (Type u) := ⟨MfldCat.carrier⟩

attribute [coe] MfldCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object of `ModelWithCorners.MfldCat I n` associated to a `C^n` manifold `X` modeled on `I`.

This is the preferred way to construct a term of `ModelWithCorners.MfldCat I n`. -/
abbrev of (X : Type u) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X] :
    MfldCat I n := ⟨X⟩

variable (X I) in
lemma coe_of : (of (I := I) (n := n) X : Type u) = X := rfl

/-- The type of morphisms in `ModelWithCorners.MfldCat I n`. -/
@[ext]
structure Hom (M N : MfldCat.{u} I n) where
  private mk ::
  /-- The underlying `C^n` map. -/
  hom' : ContMDiffMap I I M N n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (MfldCat I n) where
  Hom M N := Hom M N
  id M := ⟨ContMDiffMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (MfldCat I n)
    (fun M N => ContMDiffMap I I M N n) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `ModelWithCorners.MfldCat` back into a `ContMDiffMap`. -/
abbrev Hom.hom {M N : MfldCat I n} (f : Hom M N) :=
  ConcreteCategory.hom (C := MfldCat I n) f

/-- Typecheck a `ContMDiffMap` as a morphism in `ModelWithCorners.MfldCat`. -/
abbrev ofHom (f : ContMDiffMap I I X Y n) : of (I := I) (n := n) X ⟶ of (I := I) (n := n) Y :=
  ConcreteCategory.ofHom (C := MfldCat I n) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : MfldCat.{u} I n) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {M : MfldCat I n} :
    (𝟙 M : M ⟶ M).hom = ContMDiffMap.id := rfl

@[simp]
lemma hom_comp {M N P : MfldCat I n} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

section ofHom

@[simp]
lemma hom_ofHom (f : ContMDiffMap I I X Y n) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {M N : MfldCat I n} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id :
    ofHom (ContMDiffMap.id : ContMDiffMap I I X X n) = 𝟙 (of (I := I) (n := n) X) := rfl

@[simp]
lemma ofHom_comp (f : ContMDiffMap I I X Y n) (g : ContMDiffMap I I Y Z n) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

end ofHom

instance inhabited : Inhabited (MfldCat I n) :=
  ⟨of H⟩

/-- `ModelWithCorners.MfldCat I n` has a forgetful functor to `TopCat`. -/
instance : HasForget₂ (MfldCat I n) TopCat.{u} where
  forget₂.obj M := TopCat.of M
  forget₂.map f := TopCat.ofHom ⟨f.hom, f.hom.contMDiff.continuous⟩

/-- Any diffeomorphism induces an isomorphism in `ModelWithCorners.MfldCat`. -/
@[simps]
def isoOfDiffeomorph {M N : MfldCat I n} (f : M ≃ₘ^n⟮I, I⟯ N) : M ≅ N where
  hom := ofHom f.toContMDiffMap
  inv := ofHom f.symm.toContMDiffMap

/-- Any isomorphism in `ModelWithCorners.MfldCat` induces a diffeomorphism. -/
@[simps]
def diffeomorphOfIso {M N : MfldCat I n} (f : M ≅ N) : M ≃ₘ^n⟮I, I⟯ N where
  toFun := f.hom
  invFun := f.inv
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := f.hom.hom.contMDiff
  contMDiff_invFun := f.inv.hom.contMDiff

@[simp]
theorem of_isoOfDiffeomorph {M N : MfldCat I n} (f : M ≃ₘ^n⟮I, I⟯ N) :
    diffeomorphOfIso (isoOfDiffeomorph f) = f :=
  rfl

@[simp]
theorem of_diffeomorphOfIso {M N : MfldCat I n} (f : M ≅ N) :
    isoOfDiffeomorph (diffeomorphOfIso f) = f :=
  rfl

/-- The constant morphism `M ⟶ N` in `ModelWithCorners.MfldCat` given by `y : N`. -/
def const {M N : MfldCat I n} (y : N) : M ⟶ N :=
  ofHom <| ContMDiffMap.const y

@[simp]
lemma const_apply {M N : MfldCat I n} (y : N) (x : M) :
    const y x = y := rfl

end MfldCat

end ModelWithCorners

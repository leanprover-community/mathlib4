/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.Category.MfldCat.OfModel

/-!
# The category of `C^n` manifolds

`MfldCat 𝕜 n` is the category of `C^n` manifolds over `𝕜`, where the model with corners is allowed
to vary between objects: an object bundles a model vector space `E`, a model space `H`, a model with
corners `I : ModelWithCorners 𝕜 E H`, and a term of `ModelWithCorners.MfldCat I n` (a `C^n` manifold
modeled on `I`). Thus `MfldCat 𝕜 n` includes manifolds with boundary and corners.

The functor `MfldCat.fromModelWithCorners I n : ModelWithCorners.MfldCat I n ⥤ MfldCat 𝕜 n`
interprets a manifold modeled on a fixed `I` as an object of `MfldCat 𝕜 n`; this is how concrete
constructions performed in the fixed-model world carry over.

We also implement `HasForget₂ (MfldCat 𝕜 n) TopCat`—the forgetful functor into the category of
topological spaces—and `MfldCat.ofNormedSpace`, which realizes a normed space as a `C^n` manifold
modeled on itself.

## Implementation notes

* We do not assume `[FiniteDimensional 𝕜 E]`, `[T2Space M]` or `[SigmaCompactSpace M]`, so this
  category includes non-Hausdorff, non-paracompact and infinite-dimensional manifolds.
* We keep `E`, `H` and the underlying type of a manifold all in the same universe `u`, while `𝕜`
  is given a separate universe `v`.

## Future work

* Define a functor `FGModuleCat 𝕜 ⥤ MfldCat 𝕜 n`.
* Show that `MfldCat 𝕜 n` is a `CartesianMonoidalCategory`.
-/

public section

open CategoryTheory
open scoped Manifold ContDiff

universe u v

/-- The category of `C^n` manifolds over `𝕜`. -/
structure MfldCat (𝕜 : Type v) [NontriviallyNormedField 𝕜] (n : ℕ∞ω) where
  private mk ::
  /-- The model normed space. -/
  E : Type u
  /-- The model space. -/
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup E]
  [normedSpace : NormedSpace 𝕜 E]
  [topologicalSpaceH : TopologicalSpace H]
  /-- The model with corners. -/
  I : ModelWithCorners 𝕜 E H
  /-- The underlying `C^n` manifold, modeled on `I`. -/
  obj : ModelWithCorners.MfldCat.{u, v, u, u} I n

attribute [instance] MfldCat.normedAddCommGroup MfldCat.normedSpace MfldCat.topologicalSpaceH

initialize_simps_projections MfldCat (-normedAddCommGroup, -normedSpace, -topologicalSpaceH)

namespace MfldCat
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {M N P : MfldCat 𝕜 n}
  {X Y Z : Type u} {E E' E'' : Type u} {H H' H'' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {I'' : ModelWithCorners 𝕜 E'' H''}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' n Y]
  [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold I'' n Z]

/-- The underlying type of an object of `MfldCat 𝕜 n`. -/
abbrev carrier (M : MfldCat 𝕜 n) : Type u := M.obj.carrier

instance : CoeSort (MfldCat 𝕜 n) (Type u) := ⟨carrier⟩

attribute [coe] MfldCat.carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object of `MfldCat 𝕜 n` associated to a `C^n` manifold `X` modeled on `I`.

This is the preferred way to construct a term of `MfldCat 𝕜 n`. -/
abbrev of (X : Type u) {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u}
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I n X] : MfldCat 𝕜 n :=
  ⟨E, H, I, .of X⟩

variable (X I) in
lemma coe_of : (of (n := n) X I : Type u) = X := rfl

/-- The type of morphisms in `MfldCat 𝕜 n`. -/
@[ext]
structure Hom (M N : MfldCat.{u, v} 𝕜 n) where
  private mk ::
  /-- The underlying `C^n` map. -/
  hom' : ContMDiffMap M.I N.I M N n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (MfldCat 𝕜 n) where
  Hom M N := Hom M N
  id M := ⟨.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (MfldCat 𝕜 n) (fun M N => ContMDiffMap M.I N.I M N n) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MfldCat` back into a `ContMDiffMap`. -/
abbrev Hom.hom (f : Hom M N) := ConcreteCategory.hom (C := MfldCat 𝕜 n) f

/-- Typecheck a `ContMDiffMap` as a morphism in `MfldCat`. -/
abbrev ofHom (f : ContMDiffMap I I' X Y n) :
    of (n := n) X I ⟶ of (n := n) Y I' :=
  ConcreteCategory.ofHom (C := MfldCat 𝕜 n) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : MfldCat.{u, v} 𝕜 n) (f : Hom M N) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 M : M ⟶ M).hom = ContMDiffMap.id := rfl
@[simp] lemma hom_comp (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma id_apply (M : MfldCat 𝕜 n) (m : M) : (𝟙 M : M ⟶ M) m = m := rfl
lemma comp_apply (f : M ⟶ N) (g : N ⟶ P) (m : M) : (f ≫ g) m = g (f m) := rfl

@[ext] lemma hom_ext {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[simp] lemma hom_ofHom (f : ContMDiffMap I I' X Y n) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : M ⟶ N) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (ContMDiffMap.id : ContMDiffMap I I X X n) = 𝟙 (of X I) := rfl

@[simp]
lemma ofHom_comp (f : ContMDiffMap I I' X Y n) (g : ContMDiffMap I' I'' Y Z n) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : ContMDiffMap I I' X Y n) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by simp
lemma hom_inv_apply (e : M ≅ N) (x : N) : e.hom (e.inv x) = x := by simp

instance inhabited : Inhabited (MfldCat 𝕜 n) := ⟨of 𝕜 (modelWithCornersSelf 𝕜 𝕜)⟩

/-- A normed space is a `C^n` manifold (modeled on itself). -/
abbrev ofNormedSpace (n : ℕ∞ω) (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    MfldCat 𝕜 n :=
  of E (modelWithCornersSelf 𝕜 E)

instance hasForgetToTopCat : HasForget₂ (MfldCat 𝕜 n) TopCat.{u} where
  forget₂.obj M := .of M
  forget₂.map f := TopCat.ofHom ⟨f.hom, f.hom.contMDiff.continuous⟩

@[simp] lemma forget₂_topCat_obj (M : MfldCat 𝕜 n) :
    (forget₂ (MfldCat 𝕜 n) TopCat).obj M = .of M := rfl

@[simp] lemma forget₂_topCat_map (f : M ⟶ N) :
    (forget₂ (MfldCat 𝕜 n) TopCat).map f = TopCat.ofHom ⟨f.hom, f.hom.contMDiff.continuous⟩ := rfl

/-- Build an isomorphism in `MfldCat 𝕜 n` from a diffeomorphism. -/
@[expose, simps]
def isoOfDiffeomorph (e : M ≃ₘ^n⟮M.I, N.I⟯ N) : M ≅ N where
  hom := ofHom e.toContMDiffMap
  inv := ofHom e.symm.toContMDiffMap
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

/-- Build a diffeomorphism from an isomorphism in `MfldCat 𝕜 n`. -/
@[expose, simps]
def diffeomorphOfIso (i : M ≅ N) : M ≃ₘ^n⟮M.I, N.I⟯ N where
  toFun := i.hom
  invFun := i.inv
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := i.hom.hom.contMDiff
  contMDiff_invFun := i.inv.hom.contMDiff

/-- Diffeomorphisms are the same as isomorphisms in `MfldCat 𝕜 n`. -/
@[expose, simps]
def isoEquivDiffeomorph : (M ≅ N) ≃ (M ≃ₘ^n⟮M.I, N.I⟯ N) where
  toFun := diffeomorphOfIso
  invFun := isoOfDiffeomorph
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor interpreting a `C^n` manifold modeled on a fixed `I` as an object of `MfldCat 𝕜 n`,
where the model is allowed to vary. -/
@[expose, simps]
def fromModelWithCorners (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    ModelWithCorners.MfldCat I n ⥤ MfldCat 𝕜 n where
  obj M := of M I
  map f := ofHom f.hom

end MfldCat

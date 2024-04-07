/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!

# The functor of points

Given a scheme `X`, the functor of points associated to `X` is the functor
from the category of commutative rings to types sending `R` to
`X(R) = Hom(Spec R, X)`.

This is of course functorial in `X` as well, providing a functor
`Scheme ⥤ CommRingCat ⥤ Type`.

We construct this functor in this file. It turns out that this functor is fully faithful,
which we also prove in this file.

## Definitions:

- Given `X : Scheme`, `X.functorOfPoints` is its associated functor of points.
- `schemeToFunctor` is the functor `Scheme ⥤ CommRingCat ⥤ Type` (with suitable universes).
- `schemeToFunctor` is provided with `Full` and `Faithful` instances.

## Projects

- Notation for `X.functorOfPoints`.
- `X.functorOfPoints` is a Zariski sheaf for any `X : Scheme`.
- Characterize the essential immage of `schemeToFunctorOfPoints`.

-/

noncomputable section

namespace AlgebraicGeometry

universe u

open CategoryTheory


/-- The functor of points associated to a scheme. -/
@[simps! obj map]
def Scheme.functorOfPoints (X : Scheme.{u}) : CommRingCat.{u} ⥤ Type u :=
  Spec.rightOp ⋙ yoneda.obj X

/-- A morphism of schemes induces a morphism on the functors of points. -/
@[simps! app]
def Scheme.mapFunctorOfPoints {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  whiskerLeft _ <| yoneda.map f

@[simp]
lemma Scheme.mapFunctorOfPoints_id (X : Scheme.{u}) :
    mapFunctorOfPoints (𝟙 X) = 𝟙 _ :=
  whiskerLeft_id _

@[simp]
lemma Scheme.mapFunctorOfPoints_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapFunctorOfPoints (f ≫ g) = mapFunctorOfPoints f ≫ mapFunctorOfPoints g :=
  by simp [mapFunctorOfPoints]

/-- The "functor of points" functor, which sends `X` to `X.functorOfPoints` on objects
and `f` to `Scheme.mapFunctorOfPoints f` on morphisms. -/
@[simps]
def schemeToFunctor : Scheme.{u} ⥤ CommRingCat.{u} ⥤ Type u where
  obj X := X.functorOfPoints
  map f := Scheme.mapFunctorOfPoints f

instance : Faithful schemeToFunctor where
  map_injective := by
    intro X Y f g h
    let 𝓤 := X.affineOpenCover
    apply 𝓤.openCover.hom_ext
    intro j
    exact congr_arg (fun e => e.app (𝓤.obj j) (𝓤.map j)) h

/-- IMPLEMENTATION DETAIL: This is used to show the fullness of `schemeToFunctor`. -/
def homOfFunctorOfPoints {X Y : Scheme.{u}} (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    X ⟶ Y :=
  X.affineOpenCover.openCover.glueMorphisms (fun j => f.app _ <| X.affineOpenCover.map _) <| by
    intro i j
    apply schemeToFunctor.map_injective; ext A e : 3
    dsimp at e ⊢
    let 𝓤 := X.affineOpenCover
    obtain ⟨fst',hfst⟩ := Scheme.Spec.map_surjective
      (e ≫ (Limits.pullback.fst : Limits.pullback (𝓤.map i) (𝓤.map j) ⟶ _))
    obtain ⟨snd',hsnd⟩ := Scheme.Spec.map_surjective
      (e ≫ (Limits.pullback.snd : Limits.pullback (𝓤.map i) (𝓤.map j) ⟶ _))
    slice_lhs 1 2 => erw [← hfst]
    slice_rhs 1 2 => erw [← hsnd]
    have hi := congr_fun (f.naturality fst'.unop) (𝓤.map i)
    have hj := congr_fun (f.naturality snd'.unop) (𝓤.map j)
    dsimp at hi hj
    rw [← hi, ← hj]
    simp_rw [hfst, hsnd, Category.assoc, Limits.pullback.condition]

set_option pp.universes true in
instance functorOfPointsFull : Full schemeToFunctor where
  preimage f := homOfFunctorOfPoints f
  witness := by
    intro X Y f
    ext A e : 3
    dsimp [homOfFunctorOfPoints] at e ⊢
    let 𝓤 := X.affineCover
    let 𝓥 := 𝓤.pullbackCover e
    let 𝓦 := 𝓥.affineRefinement
    let ι : 𝓦.openCover ⟶ 𝓥 := Scheme.OpenCover.fromAffineRefinement.{u,u} 𝓥
    apply 𝓦.openCover.hom_ext
    intro j
    dsimp
    have aux : 𝓦.map j ≫ e = ι.app j ≫ Limits.pullback.snd ≫ X.affineCover.map j.fst := by
      have := ι.w j
      dsimp at this
      rw [← this, Category.assoc]
      congr 1
      apply Limits.pullback.condition
    rw [reassoc_of% aux, Scheme.OpenCover.ι_glueMorphisms]
    let ⟨w,hw⟩ := Scheme.Spec.map_surjective (𝓦.map j)
    have := congr_fun (f.naturality w.unop) e
    dsimp at this
    rw [← hw, ← this, hw, aux]
    let ⟨w,hw⟩ := Scheme.Spec.map_surjective (ι.app j ≫ Limits.pullback.snd)
    simp only [← Category.assoc, ← hw]
    exact congr_fun (f.naturality w.unop) (X.affineCover.map j.fst) |>.symm

end AlgebraicGeometry

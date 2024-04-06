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

-/

noncomputable section

namespace AlgebraicGeometry

universe u

open CategoryTheory


@[simps! obj map]
def Scheme.functorOfPoints (X : Scheme.{u}) : CommRingCat.{u} ⥤ Type u :=
  Spec.rightOp ⋙ yoneda.obj X

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

def homOfFunctorOfPoints {X Y : Scheme.{u}} (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    X ⟶ Y :=
  X.affineOpenCover.openCover.glueMorphisms (fun j => f.app _ <| X.affineOpenCover.map _) <| by
    intro i j
    apply schemeToFunctor.map_injective ; ext A e : 3
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

def Scheme.OpenCover.hom_ext_refinement
    {X Y : Scheme.{u}}
    (𝓤 : X.OpenCover) (𝓥 : Y.OpenCover)
    (f g : X ⟶ Y)
    (a : 𝓤 ⟶ 𝓥.pullbackCover f) (b : 𝓤 ⟶ 𝓥.pullbackCover g)
    (h : ∀ j : 𝓤.J,
      a.app j ≫ Limits.pullback.snd ≫ 𝓥.map _ =
      b.app j ≫ Limits.pullback.snd ≫ 𝓥.map _ ) :
    f = g := by
  apply 𝓤.hom_ext
  intro j
  specialize h j
  have ha := a.w j
  have hb := b.w j
  dsimp at ha hb
  conv_lhs => rw [← ha, Category.assoc, Limits.pullback.condition]
  conv_rhs => rw [← hb, Category.assoc, Limits.pullback.condition]
  exact h

instance : Full schemeToFunctor where
  preimage f := homOfFunctorOfPoints f
  witness := by
    intro X Y f
    ext A e : 3
    dsimp [homOfFunctorOfPoints] at e ⊢
    let 𝓤 := X.affineCover
    let 𝓥 := 𝓤.pullbackCover e
    let 𝓦 := 𝓥.affineRefinement
    let ι : 𝓦.openCover ⟶ 𝓥 := 𝓥.fromAffineRefinement
    apply 𝓦.openCover.hom_ext
    intro j
    dsimp
    have aux : 𝓦.map j ≫ e = ι.app j ≫ Limits.pullback.snd ≫ X.affineCover.map j.fst := by
      have := ι.w j
      dsimp at this
      rw [← this]
      rw [Category.assoc]
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

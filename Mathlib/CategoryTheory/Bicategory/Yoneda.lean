/-
Copyright (c) 2026 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# 2-Yoneda embedding

In this file we define the bicategorical Yoneda embedding.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory Bicategory.Opposite Opposite Pseudofunctor StrongTrans

universe w v u

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Version of `Bicategory.precomposing` viewed in the bicategory `Cat`. -/
@[simps]
def precomposingCat (a b c : B) :
    (a ⟶ b) ⥤ (Cat.of (b ⟶ c) ⟶ Cat.of (a ⟶ c)) where
  obj f := (precomp c f).toCatHom
  map η := NatTrans.toCatHom₂ ((precomposing a b c).map η)

/-- Version of `Bicategory.postcomposing` viewed in the bicategory `Cat`. -/
@[simps]
def postcomposingCat (a b c : B) : (b ⟶ c) ⥤ (Cat.of (a ⟶ b) ⟶ Cat.of (a ⟶ c)) where
  obj f := (postcomp a f).toCatHom
  map η := NatTrans.toCatHom₂ ((postcomposing a b c).map η)

/-- Left unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
def leftUnitorNatIsoCat (a b : B) : (precomposingCat _ _ b).obj (𝟙 a) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (λ_ ·)

/-- Right component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
def associatorNatIsoRightCat {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposingCat _ _ d).obj (f ≫ g) ≅
      (precomposingCat ..).obj g ≫ (precomposingCat ..).obj f :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ f g ·)

set_option backward.isDefEq.respectTransparency false in
/-- Middle component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
def associatorNatIsoMiddleCat {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    (precomposingCat ..).obj f ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj h ≫ (precomposingCat ..).obj f :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ f · h)

/-- Right unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
def rightUnitorNatIsoCat (a b : B) : (postcomposingCat a _ _).obj (𝟙 b) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (ρ_ ·)

set_option backward.isDefEq.respectTransparency false in
/-- Left component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
def associatorNatIsoLeftCat (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposingCat a ..).obj g ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj (g ≫ h) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ · g h)

set_option backward.isDefEq.respectTransparency false in
/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation.

This is only used for defining `yoneda`, after which `Bicategory.yoneda.obj` should be preferred. -/
@[simps!]
def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposingCat (unop b) (unop a) x)
  mapId a := leftUnitorNatIsoCat (unop a) x
  mapComp f g := associatorNatIsoRightCat g.unop f.unop x

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of a 1-morphism seen as a strong transformation between pseudofunctors. -/
@[simps!]
def postcomp₂ {a b : B} (f : a ⟶ b) : yoneda₀ a ⟶ yoneda₀ b where
  app x := (postcomposingCat (unop x) a b).obj f
  naturality g := associatorNatIsoMiddleCat g.unop f

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors.

This is an implementation detail, and `Bicategory.yoneda.map` should be preferred. -/
@[simps!]
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η } }

set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda pseudofunctor from `B` to `Bᵒᵖ ⥤ᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ᵖ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
@[simps!]
def yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (yoneda₀ ·) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIsoCat (unop b) a)
  mapComp f g := (isoMk (fun b ↦ associatorNatIsoLeftCat (unop b) f g)).symm

end Bicategory

end CategoryTheory

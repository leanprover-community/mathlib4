/-
Copyright (c) 2021 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Bicategory.Basic

namespace CategoryTheory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

open Bicategory

section

attribute [local simp] whisker_exchange

/-- Precomposition of a 1-morphism as a functor. -/
@[simps]
def precomp (c : B) (f : a ⟶ b) : (b ⟶ c) ⥤ (a ⟶ c) where
  obj := (f ≫ ·)
  map := (f ◁ ·)

/-- Precomposition of a 1-morphism as a functor from the category of 1-morphisms `a ⟶ b` into the
category of functors `(b ⟶ c) ⥤ (a ⟶ c)`. -/
@[simps]
def precomposing (a b c : B) : (a ⟶ b) ⥤ (b ⟶ c) ⥤ (a ⟶ c) where
  obj f := precomp c f
  map η := { app := (η ▷ ·) }
  
/-- Version of `Bicategory.precomposing` viewed in the bicategory `Cat`. -/
@[simps]
def precomposingCat (a b c : B) :
    (Cat.of (a ⟶ b)) ⟶ Cat.of ((Cat.of (b ⟶ c)) ⟶ (Cat.of (a ⟶ c))) where
  toFunctor := sorry

  -- obj f := precomp c f
  -- map η := { app := (η ▷ ·) }


/-- Version of `Bicategory.precomposing` viewed in the bicategory `Cat`. -/
@[simps]
def precomposingCat' (a b c : B) :
    (Cat.of (a ⟶ b)) ⟶ Cat.of ((b ⟶ c) ⥤ (a ⟶ c)) where
  toFunctor := sorry

/-- Postcomposition of a 1-morphism as a functor. -/
@[simps]
def postcomp (a : B) (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where
  obj := (· ≫ f)
  map := (· ▷ f)

/-- Postcomposition of a 1-morphism as a functor from the category of 1-morphisms `b ⟶ c` into the
category of functors `(a ⟶ b) ⥤ (a ⟶ c)`. -/
@[simps]
def postcomposing (a b c : B) : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) where
  obj f := postcomp a f
  map η := { app := (· ◁ η) }

/-- Left component of the associator as a natural isomorphism. -/
@[simps!]
def associatorNatIsoLeft (a : B) (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposing a ..).obj g ⋙ (postcomposing ..).obj h ≅ (postcomposing ..).obj (g ≫ h) :=
  NatIso.ofComponents (α_ · g h)

/-- Middle component of the associator as a natural isomorphism. -/
@[simps!]
def associatorNatIsoMiddle (f : a ⟶ b) (h : c ⟶ d) :
    (precomposing ..).obj f ⋙ (postcomposing ..).obj h ≅
      (postcomposing ..).obj h ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f · h)

/-- Right component of the associator as a natural isomorphism. -/
@[simps!]
def associatorNatIsoRight (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposing _ _ d).obj (f ≫ g) ≅ (precomposing ..).obj g ⋙ (precomposing ..).obj f :=
  NatIso.ofComponents (α_ f g ·)

/-- Left unitor as a natural isomorphism. -/
@[simps!]
def leftUnitorNatIso (a b : B) : (precomposing _ _ b).obj (𝟙 a) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (λ_ ·)

/-- Right unitor as a natural isomorphism. -/
@[simps!]
def rightUnitorNatIso (a b : B) : (postcomposing a _ _).obj (𝟙 b) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents (ρ_ ·)

end

end CategoryTheory

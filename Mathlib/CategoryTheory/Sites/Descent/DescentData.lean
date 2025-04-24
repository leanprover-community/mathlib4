/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Descent data

-/

universe t w v' u' v u

namespace CategoryTheory

open Category Limits Bicategory

namespace Pseudofunctor

section

variable {B C : Type*} [Bicategory B] [Bicategory C]
  (F : Pseudofunctor B C)
  {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (hfg : f ≫ g = fg)

def mapComp' : F.map fg ≅ F.map f ≫ F.map g := by
  subst hfg
  exact F.mapComp f g

@[simp]
lemma mapComp_rfl : F.mapComp' f g _ rfl = F.mapComp f g := rfl

end

variable {C : Type u} [Bicategory.{w, v} C] [IsLocallyDiscrete C]
  (F : Pseudofunctor C Cat.{v', u'})
  {ι : Type w} (X : ι → C)

structure DescentData where
  obj (i : ι) : F.obj (X i)
  iso ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
      (F.map f₁).obj (obj i₁) ≅ (F.map f₂).obj (obj i₂)
  iso_comp ⦃Y' Y : C⦄ (g : Y ⟶ Y') ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
      iso (f₁ ≫ g) (f₂ ≫ g) =
        (F.mapComp f₁ g).app _ ≪≫
          Functor.mapIso (F.map g) (iso f₁ f₂) ≪≫
            (F.mapComp f₂ g).symm.app _ := by aesop_cat
  iso_trans ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y) :
    iso f₁ f₂ ≪≫ iso f₂ f₃ = iso f₁ f₃ := by aesop_cat

namespace DescentData

variable {F X}

def mk' (obj : ∀ i, F.obj (X i))
    (hom : ∀ ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y),
      (F.map f₁).obj (obj i₁) ⟶ (F.map f₂).obj (obj i₂))
    (hom_comp : ∀ ⦃Y' Y : C⦄ (g : Y ⟶ Y') ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y),
      hom (f₁ ≫ g) (f₂ ≫ g) =
        (F.mapComp f₁ g).hom.app _ ≫
          (F.map g).map (hom f₁ f₂) ≫
            (F.mapComp f₂ g).inv.app _ := by aesop_cat)
    (hom_self : ∀ ⦃Y : C⦄ ⦃i : ι⦄ (f : X i ⟶ Y), hom f f = 𝟙 _ := by aesop_cat)
    (comp_hom : ∀ ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) (f₃ : X i₃ ⟶ Y),
      hom f₁ f₂ ≫ hom f₂ f₃ = hom f₁ f₃ := by aesop_cat) : F.DescentData X where
  obj := obj
  iso Y i₁ i₂ f₁ f₂ :=
    { hom := hom f₁ f₂
      inv := hom f₂ f₁ }

@[ext]
structure Hom (D₁ D₂ : F.DescentData X) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : X i₁ ⟶ Y) (f₂ : X i₂ ⟶ Y) :
    (F.map f₁).map (hom i₁) ≫ (D₂.iso f₁ f₂).hom =
      (D₁.iso f₁ f₂).hom ≫ (F.map f₂).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (F.DescentData X) where
  Hom := Hom
  id D := { hom i := 𝟙 _ }
  comp {D₁ D₂ D₃} φ ψ :=
    { hom i := φ.hom i ≫ ψ.hom i
      comm Y i₁ i₂ f₁ f₂ := by
        simp only [Functor.map_comp, assoc]
        rw [ψ.comm, φ.comm_assoc] }

end DescentData

def toDescentDataOfIsTerminal (X₀ : C) (hX₀ : IsInitial X₀) :
    F.obj X₀ ⥤ F.DescentData X where
  obj A :=
    { obj i := (F.map (hX₀.to (X i))).obj A
      iso Y i₁ i₂ f₁ f₂ :=
        (F.mapComp' (hX₀.to (X i₁)) f₁ (hX₀.to Y) (by simp)).symm.app A ≪≫
          (F.mapComp' (hX₀.to (X i₂)) f₂ (hX₀.to Y) (by simp)).app A
      iso_comp Y' Y g i₁ i₂ f₁ f₂ := by
        sorry }
  map {A B} f :=
    { hom i := (F.map _).map f
      comm Y i₁ i₂ f₁ f₂ := by
        dsimp
        sorry }

end Pseudofunctor

end CategoryTheory

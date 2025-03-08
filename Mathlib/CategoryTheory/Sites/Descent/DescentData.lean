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

universe w v' u' v u

namespace CategoryTheory

open Category Limits

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

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type w} (X : ι → C)

structure DescentData where
  obj (i : ι) : F.obj ⟨⟨X i⟩⟩
  iso ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) :
      (F.map ⟨f₁.op⟩).obj (obj i₁) ≅ (F.map ⟨f₂.op⟩).obj (obj i₂)
  iso_comp ⦃Y' Y : C⦄ (g : Y' ⟶ Y) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) :
      iso (g ≫ f₁) (g ≫ f₂) =
    (F.mapComp ⟨f₁.op⟩ ⟨g.op⟩).app _ ≪≫
      Functor.mapIso (F.map ⟨g.op⟩) (iso f₁ f₂) ≪≫
      (F.mapComp ⟨f₂.op⟩ ⟨g.op⟩).symm.app _
  iso_trans ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) :
    iso f₁ f₂ ≪≫ iso f₂ f₃ = iso f₁ f₃ := by aesop_cat

namespace DescentData

variable {F X}

@[ext]
structure Hom (D₁ D₂ : F.DescentData X) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) :
    (F.map ⟨f₁.op⟩).map (hom i₁) ≫ (D₂.iso f₁ f₂).hom =
      (D₁.iso f₁ f₂).hom ≫ (F.map ⟨f₂.op⟩).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (F.DescentData X) where
  Hom := Hom
  id D := { hom i := 𝟙 _ }
  comp {D₁ D₂ D₃} φ ψ :=
    { hom i := φ.hom i ≫ ψ.hom i
      comm Y i₁ i₂ f₁ f₂ := by
        dsimp
        simp only [Functor.map_comp, assoc]
        rw [ψ.comm, φ.comm_assoc] }

end DescentData

def toDescentDataOfIsTerminal (X₀ : C) (hX₀ : IsTerminal X₀) :
    F.obj ⟨⟨X₀⟩⟩ ⥤ F.DescentData X where
  obj A :=
    { obj i := (F.map (hX₀.from (X i)).op.toLoc).obj A
      iso Y i₁ i₂ f₁ f₂ :=
        (F.mapComp' (hX₀.from (X i₁)).op.toLoc f₁.op.toLoc (hX₀.from Y).op.toLoc
            --(by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsTerminal.comp_from])
            sorry).symm.app A ≪≫
          (F.mapComp' (hX₀.from (X i₂)).op.toLoc f₂.op.toLoc (hX₀.from Y).op.toLoc
            --(by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsTerminal.comp_from])
            sorry).app A
      iso_comp Y' Y g i₁ i₂ f₁ f₂ := by
        sorry }
  map {A B} f :=
    { hom i := (F.map _).map f
      comm Y i₁ i₂ f₁ f₂ := by
        dsimp
        simp
        sorry }

end Pseudofunctor

end CategoryTheory

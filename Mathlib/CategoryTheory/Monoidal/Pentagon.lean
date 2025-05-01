/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The pentagon identity as an equality of natural transformations

-/

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace NatTrans

variable (F : C ⥤ C ⥤ C) (α : bifunctorComp₁₂ F F ⟶ bifunctorComp₂₃ F F)

namespace Pentagon

-- ((X₁ ⊗ X₂) ⊗ X₃) ⊗ X₄
@[simps!]
def functor₁ : C ⥤ C ⥤ C ⥤ C ⥤ C :=
  (Functor.postcompose₃.obj F).obj (bifunctorComp₁₂ F F)

-- (X₁ ⊗ (X₂ ⊗ X₃)) ⊗ X₄
@[simps!]
def functor₂ : C ⥤ C ⥤ C ⥤ C ⥤ C :=
  (Functor.postcompose₃.obj F).obj (bifunctorComp₂₃ F F)

-- X₁ ⊗ ((X₂ ⊗ X₃) ⊗ X₄)
@[simps!]
def functor₃ : C ⥤ C ⥤ C ⥤ C ⥤ C :=
  (F ⋙ Functor.postcompose₃).flip.obj (bifunctorComp₁₂ F F)

-- X₁ ⊗ (X₂ ⊗ (X₃ ⊗ X₄))
@[simps!]
def functor₄ : C ⥤ C ⥤ C ⥤ C ⥤ C :=
  (F ⋙ Functor.postcompose₃).flip.obj (bifunctorComp₂₃ F F)

-- X₁ ⊗ (X₂ ⊗ (X₃ ⊗ X₄))
@[simps!]
def functor₅ : C ⥤ C ⥤ C ⥤ C ⥤ C :=
  bifunctorComp₁₂ F (bifunctorComp₂₃ F F)

example (X₁ X₂ X₃ X₄ : C) :
    ((((functor₁ F).obj X₁).obj X₂).obj X₃).obj X₄ =
    (F.obj ((F.obj ((F.obj X₁).obj X₂)).obj X₃)).obj X₄ := by
  dsimp

example (X₁ X₂ X₃ X₄ : C) :
    ((((functor₂ F).obj X₁).obj X₂).obj X₃).obj X₄ =
    (F.obj ((F.obj X₁).obj (((F.obj X₂).obj X₃)))).obj X₄ := by
  dsimp

example (X₁ X₂ X₃ X₄ : C) :
    ((((functor₃ F).obj X₁).obj X₂).obj X₃).obj X₄ =
    (F.obj X₁).obj ((F.obj ((F.obj X₂).obj X₃)).obj X₄) := by
  dsimp

example (X₁ X₂ X₃ X₄ : C) :
    ((((functor₄ F).obj X₁).obj X₂).obj X₃).obj X₄ =
    (F.obj X₁).obj ((F.obj X₂).obj ((F.obj X₃).obj X₄)) := by
  dsimp

example (X₁ X₂ X₃ X₄ : C) :
    ((((functor₅ F).obj X₁).obj X₂).obj X₃).obj X₄ =
    (F.obj ((F.obj X₁).obj X₂)).obj ((F.obj X₃).obj X₄) := by
  dsimp

variable {F}

@[simps!]
def natTrans₁₂ : functor₁ F ⟶ functor₂ F := (Functor.postcompose₃.obj F).map α

@[simps!]
def natTrans₂₃ : functor₂ F ⟶ functor₃ F where
  app X₁ :=
  { app X₂ :=
    { app X₃ := { app X₄ := ((α.app _).app _).app _ }
      naturality _ _ _ := (α.app X₁).naturality _ }
    naturality X₂ Y₂ f₂ := by
      ext X₃ : 2
      exact (α.app X₁).naturality ((F.map f₂).app X₃) }
  naturality X₁ Y₁ f₁ := by
    ext X₂ X₃ : 4
    exact congr_app (α.naturality f₁) ((F.obj X₂).obj X₃)

@[simps!]
def natTrans₃₄ : functor₃ F ⟶ functor₄ F := (F ⋙ Functor.postcompose₃).flip.map α

@[simps!]
def natTrans₁₅ : functor₁ F ⟶ functor₅ F where
  app X₁ :=
  { app X₂ :=
    { app X₃ := { app X₄ := ((α.app _).app _).app _ }
      naturality _ _ _ := (α.app _).naturality _ }
    naturality X₂ Y₂ f₂ := by
      ext X₃ : 2
      exact congr_app (α.naturality ((F.obj X₁).map f₂)) X₃ }
  naturality X₁ Y₁ f₁ := by
    ext X₂ : 2
    exact α.naturality ((F.map f₁).app X₂)

@[simps!]
def natTrans₅₄ : functor₅ F ⟶ functor₄ F where
  app X₁ :=
  { app X₂ :=
    { app X₃ := { app X₄ := ((α.app _).app _).app _ }
      naturality X₃ Y₃ f₃ := by
        ext X₄
        exact ((α.app X₁).app X₂).naturality ((F.map f₃).app X₄) }
    naturality X₂ Y₂ f₂ := by
      ext X₃ X₄
      exact congr_app ((α.app X₁).naturality f₂) _ }
  naturality X₁ Y₁ f₁ := by
    ext X₂ X₃ X₄
    exact congr_app (congr_app (α.naturality f₁) X₂) ((F.obj X₃).obj X₄)

end Pentagon

variable {F}

open Pentagon in
structure Pentagon : Prop where
  natTrans₁₂_comp_natTrans₂₃ :
    natTrans₁₂ α ≫ natTrans₂₃ α ≫ natTrans₃₄ α = natTrans₁₅ α ≫ natTrans₅₄ α := by aesop_cat

structure Triangle (ε : C) (leftUnitor : F.obj ε ≅ 𝟭 C)
    (rightUnitor : F.flip.obj ε ≅ 𝟭 C) : Prop where
  -- there is some little abuse of defeq here...
  triangle : ((flipFunctor _ _ _).map α).app ε ≫
    (flipFunctor _ _ _).map (whiskerRight leftUnitor.hom F.flip) =
      whiskerRight rightUnitor.hom F

end NatTrans

namespace MonoidalCategory

lemma pentagon_curriedAssociatorNatIso_hom [MonoidalCategory C] :
    NatTrans.Pentagon (curriedAssociatorNatIso C).hom where

def ofBifunctor (unit : C) (F : C ⥤ C ⥤ C) (α : bifunctorComp₁₂ F F ≅ bifunctorComp₂₃ F F)
    (leftUnitor : F.obj unit ≅ 𝟭 C) (rightUnitor : F.flip.obj unit ≅ 𝟭 C)
    (pentagon : NatTrans.Pentagon α.hom)
    (triangle : NatTrans.Triangle α.hom unit leftUnitor rightUnitor) :
    MonoidalCategory C where
  tensorUnit := unit
  tensorObj X₁ X₂ := (F.obj X₁).obj X₂
  whiskerLeft X₁ _ _ f₂ := (F.obj X₁).map f₂
  whiskerRight f₁ X₂ := (F.map f₁).app X₂
  associator X₁ X₂ X₃ := ((α.app X₁).app X₂).app X₃
  leftUnitor := leftUnitor.app
  rightUnitor := rightUnitor.app
  rightUnitor_naturality _ := rightUnitor.hom.naturality _
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    have h₁ := congr_app (congr_app (α.hom.naturality f₁) X₂) X₃
    have h₂ := congr_app ((α.hom.app Y₁).naturality f₂) X₃
    dsimp at h₁ h₂
    simp [← reassoc_of% h₁, reassoc_of% h₂]
  pentagon X₁ X₂ X₃ X₄ :=
    congr_app (congr_app (congr_app (congr_app pentagon.natTrans₁₂_comp_natTrans₂₃ X₁) X₂) X₃) X₄
  triangle X₁ X₃ :=
    congr_app (congr_app triangle.triangle X₁) X₃

end MonoidalCategory

end CategoryTheory

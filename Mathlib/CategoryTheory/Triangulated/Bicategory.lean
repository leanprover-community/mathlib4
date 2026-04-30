/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# The bicategory of triangulated categories

-/

@[expose] public section

universe v u

namespace CategoryTheory

section

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]

@[ext]
structure CommShiftNatTrans (F G : C₁ ⥤ C₂) (A : Type*) [AddMonoid A]
    [HasShift C₁ A] [HasShift C₂ A] [F.CommShift A] [G.CommShift A] where
    of ::
    natTrans : F ⟶ G
    [commShift : NatTrans.CommShift natTrans A]

attribute [instance] CommShiftNatTrans.commShift

end

open Limits

namespace Pretriangulated

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject C₃] [HasZeroObject C₄]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ] [HasShift C₄ ℤ]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₄]
  [∀ (n : ℤ), (shiftFunctor C₁ n).Additive]
  [∀ (n : ℤ), (shiftFunctor C₂ n).Additive]
  [∀ (n : ℤ), (shiftFunctor C₃ n).Additive]
  [∀ (n : ℤ), (shiftFunctor C₄ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂] [Pretriangulated C₃] [Pretriangulated C₄]

variable (C₁ C₂) in
structure TriangulatedFunctor where
  of ::
  functor : C₁ ⥤ C₂
  [commShift : functor.CommShift ℤ]
  [isTriangulated : functor.IsTriangulated]

namespace TriangulatedFunctor

attribute [instance] commShift isTriangulated

variable (C₁) in
abbrev id : TriangulatedFunctor C₁ C₁ := .of (𝟭 _)

abbrev comp (F : TriangulatedFunctor C₁ C₂) (G : TriangulatedFunctor C₂ C₃) :
    TriangulatedFunctor C₁ C₃ :=
  .of (F.functor ⋙ G.functor)

@[simps]
instance : Category (TriangulatedFunctor C₁ C₂) where
  Hom F G := CommShiftNatTrans F.functor G.functor ℤ
  id F := .of (𝟙 _)
  comp f g := .of (f.natTrans ≫ g.natTrans)

@[ext]
lemma hom_ext {F G : TriangulatedFunctor C₁ C₂} {f g : F ⟶ G}
    (h : f.natTrans = g.natTrans) : f = g :=
  CommShiftNatTrans.ext h

abbrev isoMk {F G : TriangulatedFunctor C₁ C₂} (e : F.functor ≅ G.functor)
    [NatTrans.CommShift e.hom ℤ] :
    F ≅ G where
  hom := .of e.hom
  inv := .of e.inv

end TriangulatedFunctor

end Pretriangulated

open Pretriangulated

structure TrCat where
  of ::
  Obj : Type u
  [cat : Category.{v} Obj]
  [hasZeroObject : HasZeroObject Obj]
  [hasShift : HasShift Obj ℤ]
  [preadditive : Preadditive Obj]
  [additive_shiftFunctor : ∀ (n : ℤ), (shiftFunctor Obj n).Additive]
  [pretriangulated : Pretriangulated Obj]
  [isTriangulated : IsTriangulated Obj]

namespace TrCat

attribute [instance] cat hasZeroObject hasShift preadditive
  additive_shiftFunctor pretriangulated isTriangulated

instance : CoeSort TrCat.{v, u} (Type u) :=
  ⟨TrCat.Obj⟩

@[simps id comp]
instance : CategoryStruct TrCat.{v, u} where
  Hom C₁ C₂ := TriangulatedFunctor C₁ C₂
  id C₁ := .id C₁
  comp := TriangulatedFunctor.comp

instance (C₁ C₂ : TrCat.{v, u}) :
    Category (C₁ ⟶ C₂) :=
  inferInstanceAs (Category (TriangulatedFunctor C₁ C₂))

@[ext]
lemma hom_ext {C₁ C₂ : TrCat.{v, u}} {F G : C₁ ⟶ C₂} {f g : F ⟶ G}
    (h : f.natTrans = g.natTrans) : f = g :=
  CommShiftNatTrans.ext h

@[simp]
lemma id_natTrans {C₁ C₂ : TrCat.{v, u}} (F : C₁ ⟶ C₂) :
    CommShiftNatTrans.natTrans (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_natTrans {C₁ C₂ : TrCat.{v, u}} {F G H : C₁ ⟶ C₂}
    (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).natTrans = f.natTrans ≫ g.natTrans := rfl

instance : Bicategory TrCat.{v, u} where
  homCategory := inferInstance
  whiskerLeft F _ _ f := .of (Functor.whiskerLeft F.functor f.natTrans)
  whiskerRight f F := .of (Functor.whiskerRight f.natTrans F.functor)
  -- This is the place where it is critical that the two possible
  -- ways to compose three functors must not be "identified"
  associator F G H := TriangulatedFunctor.isoMk (Functor.associator _ _ _)
  leftUnitor _ := TriangulatedFunctor.isoMk (Functor.leftUnitor _)
  rightUnitor _ := TriangulatedFunctor.isoMk (Functor.rightUnitor _)
  id_whiskerLeft _ := by ext; simp
  comp_whiskerLeft _ _ _ _ _ := by ext; simp
  whiskerRight_id _ := by ext; simp
  whiskerRight_comp _ _ _ := by ext; simp
  whisker_assoc _ _ _ _ _ := by ext; simp
  whisker_exchange _ _ := by ext; simp
  pentagon _ _ _ _ := by ext; simp
  triangle _ _ := by ext; simp

end TrCat

end CategoryTheory

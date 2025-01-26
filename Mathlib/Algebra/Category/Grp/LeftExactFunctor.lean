/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.Grp.Limits

/-!
# The functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence
-/

open CategoryTheory Limits

universe v u

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

variable (F : C ⥤ Type v) [PreservesFiniteLimits F]

section

variable (X : C)

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

#check F.map <| Limits.biprod.desc (𝟙 X) (𝟙 X)

def addCommGroup : AddCommGroup (F.obj X) := sorry

end

def lift (F : C ⥤ Type v) : C ⥤ AddCommGrp.{v} := sorry

instance : PreservesFiniteLimits (lift F) := sorry

def liftIso :
    ((LeftExactFunctor.whiskeringRight _ _ _).obj ⟨forget AddCommGrp.{v}, inferInstance⟩).obj ⟨lift F, inferInstance⟩ ≅ (⟨F, inferInstance⟩ : C ⥤ₗ Type v) := sorry

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

section

variable (F : C ⥤ AddCommGrp.{v}) [PreservesFiniteLimits F] (X : C)

def q : F.obj X ≅ @AddCommGrp.of ((F ⋙ forget _).obj X) (addCommGroup (F ⋙ forget _) X) := sorry

end

instance : Functor.IsEquivalence <|
    (LeftExactFunctor.whiskeringRight C _ _).obj ⟨forget AddCommGrp.{v}, inferInstance⟩ where
  full := sorry
  faithful := sorry
  essSurj := ⟨(⟨_, ⟨liftIso ·.1⟩⟩)⟩

end

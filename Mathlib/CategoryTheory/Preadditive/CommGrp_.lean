/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
#
-/

universe v u

namespace CategoryTheory.Preadditive

open CategoryTheory MonoidalCategory ChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [ChosenFiniteProducts C]

variable (C) in
/-- The canonical functor from an additive category into its commutative group objects. -/
@[simps]
def toCommGrp_ : C ⥤ CommGrp_ C where
  obj X :=
    { X := X
      one := 0
      mul := fst _ _ + snd _ _
      inv := -𝟙 X
      mul_assoc := by simp [add_assoc]
      mul_comm := by simp [add_comm] }
  map {X Y} f := { hom := f }

def oneDirection :
    toCommGrp_ C ⋙ CommGrp_.forget₂Grp_ _ ⋙ Grp_.forget₂Mon_ _ ⋙ Mon_.forget _ ≅ 𝟭 C :=
  Iso.refl _

def otherDirection :
    CommGrp_.forget₂Grp_ _ ⋙ Grp_.forget₂Mon_ _ ⋙ Mon_.forget _ ⋙ toCommGrp_ C ≅ 𝟭 (CommGrp_ C) := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine CommGrp_.mkIso (Iso.refl _) ?_ ?_
    · simp
      
      sorry
    · simp
      sorry
  · aesop_cat


end CategoryTheory.Preadditive

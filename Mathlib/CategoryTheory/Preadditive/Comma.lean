/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The comma category is preadditive

If we have additive functors `L : A ⥤ T` and `R : B ⥤ T` between preadditive categories,
then there is a structure of preadditive category on `Comma L R` such that addition commutes
with the left and right projections.

We then apply this to `Arrow T` for `T` a preadditive category.

## Tags

comma, arrow, preadditive
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {T : Type u₃} [Category.{v₃} T] [Preadditive T]
variable (L : A ⥤ T) [L.Additive] (R : B ⥤ T) [R.Additive]
variable {u v : Comma L R}

section Comma

namespace CommaMorphism

@[simps!]
instance : Add (u ⟶ v) where
  add α β := CommaMorphism.mk (α.left + β.left) (α.right + β.right) (by simp)
@[simps!]
instance : Sub (u ⟶ v) where
  sub α β := CommaMorphism.mk (α.left - β.left) (α.right - β.right) (by simp)
@[simps!]
instance : Zero (u ⟶ v) where
  zero := CommaMorphism.mk 0 0

@[simps!]
instance : Neg (u ⟶ v) where
  neg α := CommaMorphism.mk (-α.left) (-α.right)

end CommaMorphism

instance : AddCommGroup (u ⟶ v) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by cat_disch
  add_zero _ := by cat_disch
  add_comm _ _ := by ext <;> simp [add_comm]
  neg_add_cancel _ := by cat_disch
  nsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_nsmul, Preadditive.comp_nsmul, Preadditive.nsmul_comp])
  zsmul n α := CommaMorphism.mk (n • α.left) (n • α.right)
    (by simp [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp])
  nsmul_zero := by cat_disch
  nsmul_succ _ _ := by ext <;> dsimp <;> simp [add_nsmul]
  zsmul_zero' := by cat_disch
  zsmul_succ' _ _ := by ext <;> dsimp <;> simp [add_zsmul]
  zsmul_neg' _ _ := by ext <;> dsimp <;> simp [add_nsmul, add_zsmul]

/-- If we have additive functors `L : A ⥤ T` and `R : B ⥤ T` between preadditive categories,
then the category `Comma L R` is preadditive.
-/
instance : Preadditive (Comma L R) where

instance : (Comma.fst L R).Additive where

instance : (Comma.snd L R).Additive where

end Comma

section Arrow

/-- If a category `T` is preadditive, then so is its category of arrows.
-/
instance : Preadditive (Arrow T) := inferInstanceAs (Preadditive (Comma (𝟭 T) (𝟭 T)))

instance : (Arrow.leftFunc (C := T)).Additive :=
  inferInstanceAs ((Comma.fst (𝟭 T) (𝟭 T))).Additive

instance : (Arrow.rightFunc (C := T)).Additive :=
  inferInstanceAs ((Comma.snd (𝟭 T) (𝟭 T))).Additive

variable {u v : Arrow T}

@[simp]
lemma Arrow.Hom.add_left (α β : u ⟶ v) : (α + β).left = α.left + β.left := rfl

@[simp]
lemma Arrow.Hom.add_right (α β : u ⟶ v) : (α + β).right = α.right + β.right := rfl

@[simp]
lemma Arrow.Hom.zero_left : (0 : u ⟶ v).left = 0 := rfl

@[simp]
lemma Arrow.Hom.zero_right : (0 : u ⟶ v).right = 0 := rfl

@[simp]
lemma Arrow.Hom.neg_left (α : u ⟶ v) : (-α).left = -α.left := rfl

@[simp]
lemma Arrow.Hom.neg_right (α : u ⟶ v) : (-α).right = -α.right := rfl

end Arrow

end CategoryTheory

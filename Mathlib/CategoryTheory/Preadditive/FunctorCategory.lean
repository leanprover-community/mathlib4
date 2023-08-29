/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.CategoryTheory.Preadditive.Basic

#align_import category_theory.preadditive.functor_category from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Preadditive structure on functor categories

If `C` and `D` are categories and `D` is preadditive,
then `C ⥤ D` is also preadditive.

-/


open BigOperators

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category C] [Category D] [Preadditive D]

instance functorCategoryPreadditive : Preadditive (C ⥤ D)
    where
  homGroup F G :=
    { add := fun α β => { app := fun X => α.app X + β.app X }
      zero := { app := fun X => 0 }
      neg := fun α => { app := fun X => -α.app X }
      sub := fun α β => { app := fun X => α.app X - β.app X }
      add_assoc := by
        intros
        -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
        ext
        -- ⊢ NatTrans.app (a✝ + b✝ + c✝) x✝ = NatTrans.app (a✝ + (b✝ + c✝)) x✝
        apply add_assoc
        -- 🎉 no goals
      zero_add := by
        intros
        -- ⊢ 0 + a✝ = a✝
        ext
        -- ⊢ NatTrans.app (0 + a✝) x✝ = NatTrans.app a✝ x✝
        apply zero_add
        -- 🎉 no goals
      add_zero := by
        intros
        -- ⊢ a✝ + 0 = a✝
        ext
        -- ⊢ NatTrans.app (a✝ + 0) x✝ = NatTrans.app a✝ x✝
        apply add_zero
        -- 🎉 no goals
      add_comm := by
        intros
        -- ⊢ a✝ + b✝ = b✝ + a✝
        ext
        -- ⊢ NatTrans.app (a✝ + b✝) x✝ = NatTrans.app (b✝ + a✝) x✝
        apply add_comm
        -- ⊢ a✝ - b✝ = a✝ + -b✝
        -- 🎉 no goals
        -- ⊢ NatTrans.app (a✝ - b✝) x✝ = NatTrans.app (a✝ + -b✝) x✝
      sub_eq_add_neg := by
        -- 🎉 no goals
        intros
        ext
        -- ⊢ -a✝ + a✝ = 0
        apply sub_eq_add_neg
        -- ⊢ NatTrans.app (-a✝ + a✝) x✝ = NatTrans.app 0 x✝
      add_left_neg := by
        -- 🎉 no goals
        intros
        ext
        apply add_left_neg }
  add_comp := by
    intros
    -- ⊢ (f✝ + f'✝) ≫ g✝ = f✝ ≫ g✝ + f'✝ ≫ g✝
    ext
    -- ⊢ NatTrans.app ((f✝ + f'✝) ≫ g✝) x✝ = NatTrans.app (f✝ ≫ g✝ + f'✝ ≫ g✝) x✝
    apply add_comp
    -- 🎉 no goals
  comp_add := by
    intros
    -- ⊢ f✝ ≫ (g✝ + g'✝) = f✝ ≫ g✝ + f✝ ≫ g'✝
    ext
    -- ⊢ NatTrans.app (f✝ ≫ (g✝ + g'✝)) x✝ = NatTrans.app (f✝ ≫ g✝ + f✝ ≫ g'✝) x✝
    apply comp_add
    -- 🎉 no goals
#align category_theory.functor_category_preadditive CategoryTheory.functorCategoryPreadditive

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appHom (X : C) : (F ⟶ G) →+ (F.obj X ⟶ G.obj X)
    where
  toFun α := α.app X
  map_zero' := rfl
  map_add' _ _ := rfl
#align category_theory.nat_trans.app_hom CategoryTheory.NatTrans.appHom

@[simp]
theorem app_zero (X : C) : (0 : F ⟶ G).app X = 0 :=
  rfl
#align category_theory.nat_trans.app_zero CategoryTheory.NatTrans.app_zero

@[simp]
theorem app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X :=
  rfl
#align category_theory.nat_trans.app_add CategoryTheory.NatTrans.app_add

@[simp]
theorem app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X :=
  rfl
#align category_theory.nat_trans.app_sub CategoryTheory.NatTrans.app_sub

@[simp]
theorem app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X :=
  rfl
#align category_theory.nat_trans.app_neg CategoryTheory.NatTrans.app_neg

@[simp]
theorem app_nsmul (X : C) (α : F ⟶ G) (n : ℕ) : (n • α).app X = n • α.app X :=
  (appHom X).map_nsmul α n
#align category_theory.nat_trans.app_nsmul CategoryTheory.NatTrans.app_nsmul

@[simp]
theorem app_zsmul (X : C) (α : F ⟶ G) (n : ℤ) : (n • α).app X = n • α.app X :=
  (appHom X : (F ⟶ G) →+ (F.obj X ⟶ G.obj X)).map_zsmul α n
#align category_theory.nat_trans.app_zsmul CategoryTheory.NatTrans.app_zsmul

@[simp]
theorem app_sum {ι : Type*} (s : Finset ι) (X : C) (α : ι → (F ⟶ G)) :
    (∑ i in s, α i).app X = ∑ i in s, (α i).app X := by
  simp only [← appHom_apply, map_sum]
  -- 🎉 no goals
#align category_theory.nat_trans.app_sum CategoryTheory.NatTrans.app_sum

end NatTrans

end CategoryTheory

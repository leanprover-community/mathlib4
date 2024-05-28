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

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category C] [Category D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero := { app := fun X => 0 }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β := { app := fun X => α.app X + β.app X }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α := { app := fun X => -α.app X }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul := nsmulRec
      zsmul := zsmulRec
      sub := fun α β => { app := fun X => α.app X - β.app X }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        dsimp
        ext
        apply zero_add
      add_zero := by
        intros
        dsimp
        ext
        apply add_zero
      add_comm := by
        intros
        dsimp
        ext
        apply add_comm
      sub_eq_add_neg := by
        intros
        dsimp
        ext
        apply sub_eq_add_neg
      add_left_neg := by
        intros
        dsimp
        ext
        apply add_left_neg }
  add_comp := by
    intros
    dsimp
    ext
    apply add_comp
  comp_add := by
    intros
    dsimp
    ext
    apply comp_add
#align category_theory.functor_category_preadditive CategoryTheory.functorCategoryPreadditive

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appHom (X : C) : (F ⟶ G) →+ (F.obj X ⟶ G.obj X) where
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
theorem app_units_zsmul (X : C) (α : F ⟶ G) (n : ℤˣ) : (n • α).app X = n • α.app X := by
  apply app_zsmul

@[simp]
theorem app_sum {ι : Type*} (s : Finset ι) (X : C) (α : ι → (F ⟶ G)) :
    (∑ i ∈ s, α i).app X = ∑ i ∈ s, (α i).app X := by
  simp only [← appHom_apply, map_sum]
#align category_theory.nat_trans.app_sum CategoryTheory.NatTrans.app_sum

end NatTrans

end CategoryTheory

/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.Basic

#align_import category_theory.linear.functor_category from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Linear structure on functor categories

If `C` and `D` are categories and `D` is `R`-linear,
then `C ⥤ D` is also `R`-linear.

-/

namespace CategoryTheory

open CategoryTheory.Limits Linear

variable {R : Type*} [Semiring R]
variable {C D : Type*} [Category C] [Category D] [Preadditive D] [Linear R D]

instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G :=
    { smul := fun r α =>
        { app := fun X => r • α.app X
          naturality := by
            intros
            rw [comp_smul, smul_comp, α.naturality] }
      one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply mul_smul }
  smul_comp := by
    intros
    ext
    apply smul_comp
  comp_smul := by
    intros
    ext
    apply comp_smul
#align category_theory.functor_category_linear CategoryTheory.functorCategoryLinear

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
def appLinearMap (X : C) : (F ⟶ G) →ₗ[R] F.obj X ⟶ G.obj X where
  toFun α := α.app X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align category_theory.nat_trans.app_linear_map CategoryTheory.NatTrans.appLinearMap

@[simp]
theorem app_smul (X : C) (r : R) (α : F ⟶ G) : (r • α).app X = r • α.app X :=
  rfl
#align category_theory.nat_trans.app_smul CategoryTheory.NatTrans.app_smul

end NatTrans

end CategoryTheory

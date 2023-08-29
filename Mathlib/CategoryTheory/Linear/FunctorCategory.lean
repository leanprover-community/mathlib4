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


open BigOperators

namespace CategoryTheory

open CategoryTheory.Limits Linear

variable {R : Type*} [Semiring R]

variable {C D : Type*} [Category C] [Category D] [Preadditive D] [Linear R D]

instance functorCategoryLinear : Linear R (C ⥤ D)
    where
  homModule F G :=
    { smul := fun r α =>
        { app := fun X => r • α.app X
          naturality := by
            intros
            -- ⊢ F.map f✝ ≫ (fun X => r • NatTrans.app α X) Y✝ = (fun X => r • NatTrans.app α …
            rw [comp_smul, smul_comp, α.naturality] }
            -- 🎉 no goals
      one_smul := by
        intros
        -- ⊢ 1 • b✝ = b✝
        ext
        -- ⊢ NatTrans.app (1 • b✝) x✝ = NatTrans.app b✝ x✝
        apply one_smul
        -- 🎉 no goals
      zero_smul := by
        intros
        -- ⊢ 0 • x✝ = 0
        ext
        -- ⊢ NatTrans.app (0 • x✝¹) x✝ = NatTrans.app 0 x✝
        apply zero_smul
        -- ⊢ a✝ • 0 = 0
        -- 🎉 no goals
        -- ⊢ NatTrans.app (a✝ • 0) x✝ = NatTrans.app 0 x✝
      smul_zero := by
        -- 🎉 no goals
        intros
        ext
        -- ⊢ (r✝ + s✝) • x✝ = r✝ • x✝ + s✝ • x✝
        apply smul_zero
        -- ⊢ NatTrans.app ((r✝ + s✝) • x✝¹) x✝ = NatTrans.app (r✝ • x✝¹ + s✝ • x✝¹) x✝
      add_smul := by
        -- ⊢ a✝ • (x✝ + y✝) = a✝ • x✝ + a✝ • y✝
        -- ⊢ (x✝ * y✝) • b✝ = x✝ • y✝ • b✝
        -- 🎉 no goals
        -- ⊢ NatTrans.app ((x✝¹ * y✝) • b✝) x✝ = NatTrans.app (x✝¹ • y✝ • b✝) x✝
        -- ⊢ NatTrans.app (a✝ • (x✝¹ + y✝)) x✝ = NatTrans.app (a✝ • x✝¹ + a✝ • y✝) x✝
        -- 🎉 no goals
        intros
        -- 🎉 no goals
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
    -- ⊢ (r✝ • f✝) ≫ g✝ = r✝ • f✝ ≫ g✝
    ext
    -- ⊢ NatTrans.app ((r✝ • f✝) ≫ g✝) x✝ = NatTrans.app (r✝ • f✝ ≫ g✝) x✝
    apply smul_comp
    -- 🎉 no goals
  comp_smul := by
    intros
    -- ⊢ f✝ ≫ (r✝ • g✝) = r✝ • f✝ ≫ g✝
    ext
    -- ⊢ NatTrans.app (f✝ ≫ (r✝ • g✝)) x✝ = NatTrans.app (r✝ • f✝ ≫ g✝) x✝
    apply comp_smul
    -- 🎉 no goals
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

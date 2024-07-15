/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import category_theory.preadditive.endo_functor from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive category and `F` is an additive endofunctor on `C` then `Algebra F` is
also preadditive. Dually, the category `Coalgebra F` is also preadditive.
-/


universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (F : C ⥤ C) [Functor.Additive (F : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive endofunctor on a preadditive category is preadditive.
-/
@[simps]
instance Endofunctor.algebraPreadditive : Preadditive (Endofunctor.Algebra F) where
  homGroup A₁ A₂ :=
    { add := fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Endofunctor.Algebra.Hom.h, comp_add] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [comp_nsmul, Functor.map_nsmul, nsmul_comp, Endofunctor.Algebra.Hom.h] }
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Endofunctor.Algebra.Hom.h, comp_neg] }
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Endofunctor.Algebra.Hom.h, comp_sub] }
      zsmul := fun r α =>
        { f := r • α.f
          h := by rw [comp_zsmul, Functor.map_zsmul, zsmul_comp, Endofunctor.Algebra.Hom.h] }
      add_assoc := by
        intros
        apply Algebra.Hom.ext
        apply add_assoc
      zero_add := by
        intros
        apply Algebra.Hom.ext
        apply zero_add
      add_zero := by
        intros
        apply Algebra.Hom.ext
        apply add_zero
      nsmul_zero := by
        intros
        apply Algebra.Hom.ext
        apply zero_smul
      nsmul_succ := by
        intros
        apply Algebra.Hom.ext
        apply succ_nsmul
      sub_eq_add_neg := by
        intros
        apply Algebra.Hom.ext
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        apply Algebra.Hom.ext
        apply zero_smul
      zsmul_succ' := by
        intros
        apply Algebra.Hom.ext
        dsimp
        simp only [natCast_zsmul, succ_nsmul]
        rfl
      zsmul_neg' := by
        intros
        apply Algebra.Hom.ext
        simp only [negSucc_zsmul, neg_inj, nsmul_eq_smul_cast ℤ]
      add_left_neg := by
        intros
        apply Algebra.Hom.ext
        apply add_left_neg
      add_comm := by
        intros
        apply Algebra.Hom.ext
        apply add_comm }
  add_comp := by
    intros
    apply Algebra.Hom.ext
    apply add_comp
  comp_add := by
    intros
    apply Algebra.Hom.ext
    apply comp_add
#align category_theory.endofunctor.algebra_preadditive CategoryTheory.Endofunctor.algebraPreadditive

instance Algebra.forget_additive : (Endofunctor.Algebra.forget F).Additive where
#align category_theory.algebra.forget_additive CategoryTheory.Algebra.forget_additive

@[simps]
instance Endofunctor.coalgebraPreadditive : Preadditive (Endofunctor.Coalgebra F) where
  homGroup A₁ A₂ :=
    { add := fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Endofunctor.Coalgebra.Hom.h, add_comp] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Endofunctor.Coalgebra.Hom.h, nsmul_comp] }
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Endofunctor.Coalgebra.Hom.h, neg_comp] }
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Endofunctor.Coalgebra.Hom.h, sub_comp] }
      zsmul := fun r α =>
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Endofunctor.Coalgebra.Hom.h, zsmul_comp] }
      add_assoc := by
        intros
        apply Coalgebra.Hom.ext
        apply add_assoc
      zero_add := by
        intros
        apply Coalgebra.Hom.ext
        apply zero_add
      add_zero := by
        intros
        apply Coalgebra.Hom.ext
        apply add_zero
      nsmul_zero := by
        intros
        apply Coalgebra.Hom.ext
        apply zero_smul
      nsmul_succ := by
        intros
        apply Coalgebra.Hom.ext
        apply succ_nsmul
      sub_eq_add_neg := by
        intros
        apply Coalgebra.Hom.ext
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        apply Coalgebra.Hom.ext
        apply zero_smul
      zsmul_succ' := by
        intros
        apply Coalgebra.Hom.ext
        dsimp
        simp only [natCast_zsmul, succ_nsmul]
        rfl
      zsmul_neg' := by
        intros
        apply Coalgebra.Hom.ext
        simp only [negSucc_zsmul, neg_inj, nsmul_eq_smul_cast ℤ]
      add_left_neg := by
        intros
        apply Coalgebra.Hom.ext
        apply add_left_neg
      add_comm := by
        intros
        apply Coalgebra.Hom.ext
        apply add_comm }
  add_comp := by
    intros
    apply Coalgebra.Hom.ext
    apply add_comp
  comp_add := by
    intros
    apply Coalgebra.Hom.ext
    apply comp_add
#align category_theory.endofunctor.coalgebra_preadditive CategoryTheory.Endofunctor.coalgebraPreadditive

instance Coalgebra.forget_additive : (Endofunctor.Coalgebra.forget F).Additive where
#align category_theory.coalgebra.forget_additive CategoryTheory.Coalgebra.forget_additive

end CategoryTheory

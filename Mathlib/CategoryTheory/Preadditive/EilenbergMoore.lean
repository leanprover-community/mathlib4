/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive category and `T` is an additive monad on `C` then `Algebra T` is also
preadditive. Dually, if `U` is an additive comonad on `C` then `Coalgebra U` is preadditive as well.

-/


universe v₁ u₁

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (T : Monad C)
  [Functor.Additive (T : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive monad on a preadditive category is preadditive. -/
@[simps]
instance Monad.algebraPreadditive : Preadditive (Monad.Algebra T) where
  homGroup F G :=
    { add := fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Monad.Algebra.Hom.h, comp_add] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, nsmul_comp, Monad.Algebra.Hom.h, comp_nsmul] }
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Monad.Algebra.Hom.h, comp_neg] }
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Monad.Algebra.Hom.h, comp_sub] }
      zsmul := fun r α =>
        { f := r • α.f
          h := by rw [Functor.map_zsmul, zsmul_comp, Monad.Algebra.Hom.h, comp_zsmul] }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        ext
        apply zero_add
      add_zero := by
        intros
        ext
        apply add_zero
      nsmul_zero := by
        intros
        ext
        apply zero_smul
      nsmul_succ := by
        intros
        ext
        apply succ_nsmul
      sub_eq_add_neg := by
        intros
        ext
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        ext
        apply zero_smul
      zsmul_succ' := by
        intros
        ext
        simp only [natCast_zsmul, succ_nsmul]
        rfl
      zsmul_neg' := by
        intros
        ext
        simp only [negSucc_zsmul, ← Nat.cast_smul_eq_nsmul ℤ]
      neg_add_cancel := by
        intros
        ext
        apply neg_add_cancel
      add_comm := by
        intros
        ext
        apply add_comm }
  add_comp := by
    intros
    ext
    apply add_comp
  comp_add := by
    intros
    ext
    apply comp_add

instance Monad.forget_additive : (Monad.forget T).Additive where

variable (U : Comonad C) [Functor.Additive (U : C ⥤ C)]

/-- The category of coalgebras over an additive comonad on a preadditive category is preadditive. -/
@[simps]
instance Comonad.coalgebraPreadditive : Preadditive (Comonad.Coalgebra U) where
  homGroup F G :=
    { add := fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Comonad.Coalgebra.Hom.h, add_comp] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, comp_zero, zero_comp] }
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Comonad.Coalgebra.Hom.h, nsmul_comp] }
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Comonad.Coalgebra.Hom.h, neg_comp] }
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Comonad.Coalgebra.Hom.h, sub_comp] }
      zsmul := fun r α =>
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Comonad.Coalgebra.Hom.h, zsmul_comp] }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        ext
        apply zero_add
      add_zero := by
        intros
        ext
        apply add_zero
      nsmul_zero := by
        intros
        ext
        apply zero_smul
      nsmul_succ := by
        intros
        ext
        apply succ_nsmul
      sub_eq_add_neg := by
        intros
        ext
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        ext
        apply zero_smul
      zsmul_succ' := by
        intros
        ext
        simp only [natCast_zsmul, succ_nsmul]
        rfl
      zsmul_neg' := by
        intros
        ext
        simp only [negSucc_zsmul, ← Nat.cast_smul_eq_nsmul ℤ]
      neg_add_cancel := by
        intros
        ext
        apply neg_add_cancel
      add_comm := by
        intros
        ext
        apply add_comm }
  add_comp := by
    intros
    ext
    apply add_comp
  comp_add := by
    intros
    ext
    apply comp_add

instance Comonad.forget_additive : (Comonad.forget U).Additive where

end CategoryTheory

/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Preadditive structure on algebras over a monad

If `C` is a preadditive category and `T` is an additive monad on `C` then `Algebra T` is also
preadditive. Dually, if `U` is an additive comonad on `C` then `Coalgebra U` is preadditive as well.

-/

public section


universe v₁ u₁

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] (T : Monad C)
  [Functor.Additive (T : C ⥤ C)]

open CategoryTheory.Limits Preadditive

/-- The category of algebras over an additive monad on a preadditive category is preadditive. -/
@[simps]
instance Monad.algebraPreadditive : Preadditive (Monad.Algebra T) where
  homGroup F G :=
    { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, add_comp, Monad.Algebra.Hom.h, comp_add] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [Functor.map_nsmul, nsmul_comp, Monad.Algebra.Hom.h, comp_nsmul] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Monad.Algebra.Hom.h, comp_neg] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Monad.Algebra.Hom.h, comp_sub] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [Functor.map_zsmul, zsmul_comp, Monad.Algebra.Hom.h, comp_zsmul] }
      add_assoc _ _ _ := Algebra.Hom.ext <| add_assoc _ _ _
      zero_add _ := Algebra.Hom.ext <| zero_add _
      add_zero _ := Algebra.Hom.ext <| add_zero _
      nsmul_zero _ := Algebra.Hom.ext <| zero_nsmul _
      nsmul_succ _ _ := Algebra.Hom.ext <| succ_nsmul _ _
      sub_eq_add_neg _ _ := Algebra.Hom.ext <| sub_eq_add_neg _ _
      zsmul_zero' _ := Algebra.Hom.ext <| zero_zsmul _
      zsmul_succ' _ _ := Algebra.Hom.ext <| SubNegMonoid.zsmul_succ' _ _
      zsmul_neg' _ _ := Algebra.Hom.ext <| SubNegMonoid.zsmul_neg' _ _
      neg_add_cancel _ := Algebra.Hom.ext <| neg_add_cancel _
      add_comm _ _ := Algebra.Hom.ext <| add_comm _ _ }
  add_comp _ _ _ _ _ _ := Algebra.Hom.ext <| add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := Algebra.Hom.ext <| comp_add _ _ _ _ _ _

instance Monad.forget_additive : (Monad.forget T).Additive where

variable (U : Comonad C) [Functor.Additive (U : C ⥤ C)]

/-- The category of coalgebras over an additive comonad on a preadditive category is preadditive. -/
@[simps]
instance Comonad.coalgebraPreadditive : Preadditive (Comonad.Coalgebra U) where
  homGroup F G :=
    { add α β :=
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Comonad.Coalgebra.Hom.h, add_comp] }
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, comp_zero, zero_comp] }
      nsmul n α :=
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Comonad.Coalgebra.Hom.h, nsmul_comp] }
      neg α :=
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Comonad.Coalgebra.Hom.h, neg_comp] }
      sub α β :=
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Comonad.Coalgebra.Hom.h, sub_comp] }
      zsmul r α :=
        { f := r • α.f
          h := by rw [Functor.map_zsmul, comp_zsmul, Comonad.Coalgebra.Hom.h, zsmul_comp] }
      add_assoc _ _ _ := Coalgebra.Hom.ext <| add_assoc _ _ _
      zero_add _ := Coalgebra.Hom.ext <| zero_add _
      add_zero _ := Coalgebra.Hom.ext <| add_zero _
      nsmul_zero _ := Coalgebra.Hom.ext <| zero_nsmul _
      nsmul_succ _ _ := Coalgebra.Hom.ext <| succ_nsmul _ _
      sub_eq_add_neg _ _ := Coalgebra.Hom.ext <| sub_eq_add_neg _ _
      zsmul_zero' _ := Coalgebra.Hom.ext <| zero_zsmul _
      zsmul_succ' _ _ := Coalgebra.Hom.ext <| SubNegMonoid.zsmul_succ' _ _
      zsmul_neg' _ _ := Coalgebra.Hom.ext <| SubNegMonoid.zsmul_neg' _ _
      neg_add_cancel _ := Coalgebra.Hom.ext <| neg_add_cancel _
      add_comm _ _ := Coalgebra.Hom.ext <| add_comm _ _ }
  add_comp _ _ _ _ _ _ := Coalgebra.Hom.ext <| add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := Coalgebra.Hom.ext <| comp_add _ _ _ _ _ _

instance Comonad.forget_additive : (Comonad.forget U).Additive where

end CategoryTheory

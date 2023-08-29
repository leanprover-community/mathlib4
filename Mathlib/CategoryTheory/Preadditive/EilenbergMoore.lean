/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import category_theory.preadditive.eilenberg_moore from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

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
                  -- 🎉 no goals
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
                  -- 🎉 no goals
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, nsmul_comp, Monad.Algebra.Hom.h, comp_nsmul] }
                  -- 🎉 no goals
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Monad.Algebra.Hom.h, comp_neg] }
                  -- 🎉 no goals
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Monad.Algebra.Hom.h, comp_sub] }
                  -- 🎉 no goals
      zsmul := fun r α =>
        -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
        { f := r • α.f
        -- ⊢ (a✝ + b✝ + c✝).f = (a✝ + (b✝ + c✝)).f
          h := by rw [Functor.map_zsmul, zsmul_comp, Monad.Algebra.Hom.h, comp_zsmul] }
        -- 🎉 no goals
                  -- 🎉 no goals
      add_assoc := by
        intros
        -- ⊢ 0 + a✝ = a✝
        ext
        -- ⊢ (0 + a✝).f = a✝.f
        apply add_assoc
        -- 🎉 no goals
      zero_add := by
        intros
        -- ⊢ a✝ + 0 = a✝
        ext
        -- ⊢ (a✝ + 0).f = a✝.f
        apply zero_add
        -- 🎉 no goals
      add_zero := by
        intros
        ext
        -- ⊢ (fun n α => Algebra.Hom.mk (n • α.f)) 0 x✝ = 0
        apply add_zero
        -- ⊢ ((fun n α => Algebra.Hom.mk (n • α.f)) 0 x✝).f = 0.f
      nsmul_zero := by
        -- 🎉 no goals
        intros
        ext
        -- ⊢ (fun n α => Algebra.Hom.mk (n • α.f)) (n✝ + 1) x✝ = x✝ + (fun n α => Algebra …
        apply zero_smul
        -- ⊢ ((fun n α => Algebra.Hom.mk (n • α.f)) (n✝ + 1) x✝).f = (x✝ + (fun n α => Al …
      nsmul_succ := by
        -- 🎉 no goals
        intros
        ext
        apply succ_nsmul
      sub_eq_add_neg := by
        -- ⊢ a✝ - b✝ = a✝ + -b✝
        intros
        -- ⊢ (a✝ - b✝).f = (a✝ + -b✝).f
        ext
        -- 🎉 no goals
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        -- ⊢ (fun r α => Algebra.Hom.mk (r • α.f)) 0 a✝ = 0
        ext
        -- ⊢ ((fun r α => Algebra.Hom.mk (r • α.f)) 0 a✝).f = 0.f
        apply zero_smul
        -- 🎉 no goals
      zsmul_succ' := by
        intros
        -- ⊢ (fun r α => Algebra.Hom.mk (r • α.f)) (Int.ofNat (Nat.succ n✝)) a✝ = a✝ + (f …
        ext
        -- ⊢ ((fun r α => Algebra.Hom.mk (r • α.f)) (Int.ofNat (Nat.succ n✝)) a✝).f = (a✝ …
        dsimp
        -- ⊢ ↑(Nat.succ n✝) • a✝.f = (a✝ + Algebra.Hom.mk (↑n✝ • a✝.f)).f
        simp only [coe_nat_zsmul, succ_nsmul]
        -- ⊢ a✝.f + n✝ • a✝.f = (a✝ + Algebra.Hom.mk (n✝ • a✝.f)).f
        rfl
        -- 🎉 no goals
      zsmul_neg' := by
        intros
        -- ⊢ (fun r α => Algebra.Hom.mk (r • α.f)) (Int.negSucc n✝) a✝ = -(fun r α => Alg …
        ext
        -- ⊢ ((fun r α => Algebra.Hom.mk (r • α.f)) (Int.negSucc n✝) a✝).f = (-(fun r α = …
        simp only [negSucc_zsmul, neg_inj, nsmul_eq_smul_cast ℤ]
        -- 🎉 no goals
      add_left_neg := by
        intros
        -- ⊢ -a✝ + a✝ = 0
        ext
        -- ⊢ (-a✝ + a✝).f = 0.f
        apply add_left_neg
        -- 🎉 no goals
      add_comm := by
        intros
        -- ⊢ a✝ + b✝ = b✝ + a✝
        ext
        -- ⊢ (a✝ + b✝).f = (b✝ + a✝).f
        apply add_comm }
        -- 🎉 no goals
  add_comp := by
    intros
    -- ⊢ (f✝ + f'✝) ≫ g✝ = f✝ ≫ g✝ + f'✝ ≫ g✝
    ext
    -- ⊢ ((f✝ + f'✝) ≫ g✝).f = (f✝ ≫ g✝ + f'✝ ≫ g✝).f
    apply add_comp
    -- 🎉 no goals
  comp_add := by
    intros
    -- ⊢ f✝ ≫ (g✝ + g'✝) = f✝ ≫ g✝ + f✝ ≫ g'✝
    ext
    -- ⊢ (f✝ ≫ (g✝ + g'✝)).f = (f✝ ≫ g✝ + f✝ ≫ g'✝).f
    apply comp_add
    -- 🎉 no goals
#align category_theory.monad.algebra_preadditive CategoryTheory.Monad.algebraPreadditive

instance Monad.forget_additive : (Monad.forget T).Additive where
#align category_theory.monad.forget_additive CategoryTheory.Monad.forget_additive

variable (U : Comonad C) [Functor.Additive (U : C ⥤ C)]

/-- The category of coalgebras over an additive comonad on a preadditive category is preadditive. -/
@[simps]
instance Comonad.coalgebraPreadditive : Preadditive (Comonad.Coalgebra U) where
  homGroup F G :=
    { add := fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Comonad.Coalgebra.Hom.h, add_comp] }
                  -- 🎉 no goals
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, comp_zero, zero_comp] }
                  -- 🎉 no goals
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Comonad.Coalgebra.Hom.h, nsmul_comp] }
                  -- 🎉 no goals
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Comonad.Coalgebra.Hom.h, neg_comp] }
                  -- 🎉 no goals
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Comonad.Coalgebra.Hom.h, sub_comp] }
                  -- 🎉 no goals
      zsmul := fun r α =>
        -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
        { f := r • α.f
        -- ⊢ (a✝ + b✝ + c✝).f = (a✝ + (b✝ + c✝)).f
          h := by rw [Functor.map_zsmul, comp_zsmul, Comonad.Coalgebra.Hom.h, zsmul_comp] }
        -- 🎉 no goals
                  -- 🎉 no goals
      add_assoc := by
        intros
        -- ⊢ 0 + a✝ = a✝
        ext
        -- ⊢ (0 + a✝).f = a✝.f
        apply add_assoc
        -- 🎉 no goals
      zero_add := by
        intros
        -- ⊢ a✝ + 0 = a✝
        ext
        -- ⊢ (a✝ + 0).f = a✝.f
        apply zero_add
        -- 🎉 no goals
      add_zero := by
        intros
        ext
        -- ⊢ (fun n α => Coalgebra.Hom.mk (n • α.f)) 0 x✝ = 0
        apply add_zero
        -- ⊢ ((fun n α => Coalgebra.Hom.mk (n • α.f)) 0 x✝).f = 0.f
      nsmul_zero := by
        -- 🎉 no goals
        intros
        ext
        -- ⊢ (fun n α => Coalgebra.Hom.mk (n • α.f)) (n✝ + 1) x✝ = x✝ + (fun n α => Coalg …
        apply zero_smul
        -- ⊢ ((fun n α => Coalgebra.Hom.mk (n • α.f)) (n✝ + 1) x✝).f = (x✝ + (fun n α =>  …
      nsmul_succ := by
        -- 🎉 no goals
        intros
        ext
        apply succ_nsmul
      sub_eq_add_neg := by
        -- ⊢ a✝ - b✝ = a✝ + -b✝
        intros
        -- ⊢ (a✝ - b✝).f = (a✝ + -b✝).f
        ext
        -- 🎉 no goals
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        -- ⊢ (fun r α => Coalgebra.Hom.mk (r • α.f)) 0 a✝ = 0
        ext
        -- ⊢ ((fun r α => Coalgebra.Hom.mk (r • α.f)) 0 a✝).f = 0.f
        apply zero_smul
        -- 🎉 no goals
      zsmul_succ' := by
        intros
        -- ⊢ (fun r α => Coalgebra.Hom.mk (r • α.f)) (Int.ofNat (Nat.succ n✝)) a✝ = a✝ +  …
        ext
        -- ⊢ ((fun r α => Coalgebra.Hom.mk (r • α.f)) (Int.ofNat (Nat.succ n✝)) a✝).f = ( …
        dsimp
        -- ⊢ ↑(Nat.succ n✝) • a✝.f = (a✝ + Coalgebra.Hom.mk (↑n✝ • a✝.f)).f
        simp only [coe_nat_zsmul, succ_nsmul]
        -- ⊢ a✝.f + n✝ • a✝.f = (a✝ + Coalgebra.Hom.mk (n✝ • a✝.f)).f
        rfl
        -- 🎉 no goals
      zsmul_neg' := by
        intros
        -- ⊢ (fun r α => Coalgebra.Hom.mk (r • α.f)) (Int.negSucc n✝) a✝ = -(fun r α => C …
        ext
        -- ⊢ ((fun r α => Coalgebra.Hom.mk (r • α.f)) (Int.negSucc n✝) a✝).f = (-(fun r α …
        simp only [negSucc_zsmul, neg_inj, nsmul_eq_smul_cast ℤ]
        -- 🎉 no goals
      add_left_neg := by
        intros
        -- ⊢ -a✝ + a✝ = 0
        ext
        -- ⊢ (-a✝ + a✝).f = 0.f
        apply add_left_neg
        -- 🎉 no goals
      add_comm := by
        intros
        -- ⊢ a✝ + b✝ = b✝ + a✝
        ext
        -- ⊢ (a✝ + b✝).f = (b✝ + a✝).f
        apply add_comm }
        -- 🎉 no goals
  add_comp := by
    intros
    -- ⊢ (f✝ + f'✝) ≫ g✝ = f✝ ≫ g✝ + f'✝ ≫ g✝
    ext
    -- ⊢ ((f✝ + f'✝) ≫ g✝).f = (f✝ ≫ g✝ + f'✝ ≫ g✝).f
    apply add_comp
    -- 🎉 no goals
  comp_add := by
    intros
    -- ⊢ f✝ ≫ (g✝ + g'✝) = f✝ ≫ g✝ + f✝ ≫ g'✝
    ext
    -- ⊢ (f✝ ≫ (g✝ + g'✝)).f = (f✝ ≫ g✝ + f✝ ≫ g'✝).f
    apply comp_add
    -- 🎉 no goals
#align category_theory.comonad.coalgebra_preadditive CategoryTheory.Comonad.coalgebraPreadditive

instance Comonad.forget_additive : (Comonad.forget U).Additive where
#align category_theory.comonad.forget_additive CategoryTheory.Comonad.forget_additive

end CategoryTheory

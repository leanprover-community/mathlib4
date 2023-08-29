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
                  -- 🎉 no goals
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
                  -- 🎉 no goals
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [comp_nsmul, Functor.map_nsmul, nsmul_comp, Endofunctor.Algebra.Hom.h] }
                  -- 🎉 no goals
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, neg_comp, Endofunctor.Algebra.Hom.h, comp_neg] }
                  -- 🎉 no goals
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, sub_comp, Endofunctor.Algebra.Hom.h, comp_sub] }
                  -- 🎉 no goals
      zsmul := fun r α =>
        -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
        { f := r • α.f
        -- ⊢ (a✝ + b✝ + c✝).f = (a✝ + (b✝ + c✝)).f
          h := by rw [comp_zsmul, Functor.map_zsmul, zsmul_comp, Endofunctor.Algebra.Hom.h] }
        -- 🎉 no goals
                  -- 🎉 no goals
      add_assoc := by
        intros
        -- ⊢ 0 + a✝ = a✝
        apply Algebra.Hom.ext
        -- ⊢ (0 + a✝).f = a✝.f
        apply add_assoc
        -- 🎉 no goals
      zero_add := by
        intros
        -- ⊢ a✝ + 0 = a✝
        apply Algebra.Hom.ext
        -- ⊢ (a✝ + 0).f = a✝.f
        apply zero_add
        -- 🎉 no goals
      add_zero := by
        intros
        apply Algebra.Hom.ext
        -- ⊢ (fun n α => Algebra.Hom.mk (n • α.f)) 0 x✝ = 0
        apply add_zero
        -- ⊢ ((fun n α => Algebra.Hom.mk (n • α.f)) 0 x✝).f = 0.f
      nsmul_zero := by
        -- 🎉 no goals
        intros
        apply Algebra.Hom.ext
        -- ⊢ (fun n α => Algebra.Hom.mk (n • α.f)) (n✝ + 1) x✝ = x✝ + (fun n α => Algebra …
        apply zero_smul
        -- ⊢ ((fun n α => Algebra.Hom.mk (n • α.f)) (n✝ + 1) x✝).f = (x✝ + (fun n α => Al …
      nsmul_succ := by
        -- 🎉 no goals
        intros
        apply Algebra.Hom.ext
        apply succ_nsmul
      sub_eq_add_neg := by
        -- ⊢ a✝ - b✝ = a✝ + -b✝
        intros
        -- ⊢ (a✝ - b✝).f = (a✝ + -b✝).f
        apply Algebra.Hom.ext
        -- 🎉 no goals
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        -- ⊢ (fun r α => Algebra.Hom.mk (r • α.f)) 0 a✝ = 0
        apply Algebra.Hom.ext
        -- ⊢ ((fun r α => Algebra.Hom.mk (r • α.f)) 0 a✝).f = 0.f
        apply zero_smul
        -- 🎉 no goals
      zsmul_succ' := by
        intros
        -- ⊢ (fun r α => Algebra.Hom.mk (r • α.f)) (Int.ofNat (Nat.succ n✝)) a✝ = a✝ + (f …
        apply Algebra.Hom.ext
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
        apply Algebra.Hom.ext
        -- ⊢ ((fun r α => Algebra.Hom.mk (r • α.f)) (Int.negSucc n✝) a✝).f = (-(fun r α = …
        simp only [negSucc_zsmul, neg_inj, nsmul_eq_smul_cast ℤ]
        -- 🎉 no goals
      add_left_neg := by
        intros
        -- ⊢ -a✝ + a✝ = 0
        apply Algebra.Hom.ext
        -- ⊢ (-a✝ + a✝).f = 0.f
        apply add_left_neg
        -- 🎉 no goals
      add_comm := by
        intros
        -- ⊢ a✝ + b✝ = b✝ + a✝
        apply Algebra.Hom.ext
        -- ⊢ (a✝ + b✝).f = (b✝ + a✝).f
        apply add_comm }
        -- 🎉 no goals
  add_comp := by
    intros
    -- ⊢ (f✝ + f'✝) ≫ g✝ = f✝ ≫ g✝ + f'✝ ≫ g✝
    apply Algebra.Hom.ext
    -- ⊢ ((f✝ + f'✝) ≫ g✝).f = (f✝ ≫ g✝ + f'✝ ≫ g✝).f
    apply add_comp
    -- 🎉 no goals
  comp_add := by
    intros
    -- ⊢ f✝ ≫ (g✝ + g'✝) = f✝ ≫ g✝ + f✝ ≫ g'✝
    apply Algebra.Hom.ext
    -- ⊢ (f✝ ≫ (g✝ + g'✝)).f = (f✝ ≫ g✝ + f✝ ≫ g'✝).f
    apply comp_add
    -- 🎉 no goals
#align category_theory.endofunctor.algebra_preadditive CategoryTheory.Endofunctor.algebraPreadditive

instance Algebra.forget_additive : (Endofunctor.Algebra.forget F).Additive where
#align category_theory.algebra.forget_additive CategoryTheory.Algebra.forget_additive

@[simps]
instance Endofunctor.coalgebraPreadditive : Preadditive (Endofunctor.Coalgebra F) where
  homGroup A₁ A₂ :=
    { add := fun α β =>
        { f := α.f + β.f
          h := by simp only [Functor.map_add, comp_add, Endofunctor.Coalgebra.Hom.h, add_comp] }
                  -- 🎉 no goals
      zero :=
        { f := 0
          h := by simp only [Functor.map_zero, zero_comp, comp_zero] }
                  -- 🎉 no goals
      nsmul := fun n α =>
        { f := n • α.f
          h := by rw [Functor.map_nsmul, comp_nsmul, Endofunctor.Coalgebra.Hom.h, nsmul_comp] }
                  -- 🎉 no goals
      neg := fun α =>
        { f := -α.f
          h := by simp only [Functor.map_neg, comp_neg, Endofunctor.Coalgebra.Hom.h, neg_comp] }
                  -- 🎉 no goals
      sub := fun α β =>
        { f := α.f - β.f
          h := by simp only [Functor.map_sub, comp_sub, Endofunctor.Coalgebra.Hom.h, sub_comp] }
                  -- 🎉 no goals
      zsmul := fun r α =>
        -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
        { f := r • α.f
        -- ⊢ (a✝ + b✝ + c✝).f = (a✝ + (b✝ + c✝)).f
          h := by rw [Functor.map_zsmul, comp_zsmul, Endofunctor.Coalgebra.Hom.h, zsmul_comp] }
        -- 🎉 no goals
                  -- 🎉 no goals
      add_assoc := by
        intros
        -- ⊢ 0 + a✝ = a✝
        apply Coalgebra.Hom.ext
        -- ⊢ (0 + a✝).f = a✝.f
        apply add_assoc
        -- 🎉 no goals
      zero_add := by
        intros
        -- ⊢ a✝ + 0 = a✝
        apply Coalgebra.Hom.ext
        -- ⊢ (a✝ + 0).f = a✝.f
        apply zero_add
        -- 🎉 no goals
      add_zero := by
        intros
        apply Coalgebra.Hom.ext
        -- ⊢ (fun n α => Coalgebra.Hom.mk (n • α.f)) 0 x✝ = 0
        apply add_zero
        -- ⊢ ((fun n α => Coalgebra.Hom.mk (n • α.f)) 0 x✝).f = 0.f
      nsmul_zero := by
        -- 🎉 no goals
        intros
        apply Coalgebra.Hom.ext
        -- ⊢ (fun n α => Coalgebra.Hom.mk (n • α.f)) (n✝ + 1) x✝ = x✝ + (fun n α => Coalg …
        apply zero_smul
        -- ⊢ ((fun n α => Coalgebra.Hom.mk (n • α.f)) (n✝ + 1) x✝).f = (x✝ + (fun n α =>  …
      nsmul_succ := by
        -- 🎉 no goals
        intros
        apply Coalgebra.Hom.ext
        apply succ_nsmul
      sub_eq_add_neg := by
        -- ⊢ a✝ - b✝ = a✝ + -b✝
        intros
        -- ⊢ (a✝ - b✝).f = (a✝ + -b✝).f
        apply Coalgebra.Hom.ext
        -- 🎉 no goals
        apply sub_eq_add_neg
      zsmul_zero' := by
        intros
        -- ⊢ (fun r α => Coalgebra.Hom.mk (r • α.f)) 0 a✝ = 0
        apply Coalgebra.Hom.ext
        -- ⊢ ((fun r α => Coalgebra.Hom.mk (r • α.f)) 0 a✝).f = 0.f
        apply zero_smul
        -- 🎉 no goals
      zsmul_succ' := by
        intros
        -- ⊢ (fun r α => Coalgebra.Hom.mk (r • α.f)) (Int.ofNat (Nat.succ n✝)) a✝ = a✝ +  …
        apply Coalgebra.Hom.ext
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
        apply Coalgebra.Hom.ext
        -- ⊢ ((fun r α => Coalgebra.Hom.mk (r • α.f)) (Int.negSucc n✝) a✝).f = (-(fun r α …
        simp only [negSucc_zsmul, neg_inj, nsmul_eq_smul_cast ℤ]
        -- 🎉 no goals
      add_left_neg := by
        intros
        -- ⊢ -a✝ + a✝ = 0
        apply Coalgebra.Hom.ext
        -- ⊢ (-a✝ + a✝).f = 0.f
        apply add_left_neg
        -- 🎉 no goals
      add_comm := by
        intros
        -- ⊢ a✝ + b✝ = b✝ + a✝
        apply Coalgebra.Hom.ext
        -- ⊢ (a✝ + b✝).f = (b✝ + a✝).f
        apply add_comm }
        -- 🎉 no goals
  add_comp := by
    intros
    -- ⊢ (f✝ + f'✝) ≫ g✝ = f✝ ≫ g✝ + f'✝ ≫ g✝
    apply Coalgebra.Hom.ext
    -- ⊢ ((f✝ + f'✝) ≫ g✝).f = (f✝ ≫ g✝ + f'✝ ≫ g✝).f
    apply add_comp
    -- 🎉 no goals
  comp_add := by
    intros
    -- ⊢ f✝ ≫ (g✝ + g'✝) = f✝ ≫ g✝ + f✝ ≫ g'✝
    apply Coalgebra.Hom.ext
    -- ⊢ (f✝ ≫ (g✝ + g'✝)).f = (f✝ ≫ g✝ + f✝ ≫ g'✝).f
    apply comp_add
    -- 🎉 no goals
#align category_theory.endofunctor.coalgebra_preadditive CategoryTheory.Endofunctor.coalgebraPreadditive

instance Coalgebra.forget_additive : (Endofunctor.Coalgebra.forget F).Additive where
#align category_theory.coalgebra.forget_additive CategoryTheory.Coalgebra.forget_additive

end CategoryTheory

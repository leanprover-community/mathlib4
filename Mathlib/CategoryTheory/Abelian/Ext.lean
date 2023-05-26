/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz

! This file was ported from Lean 3 source module category_theory.abelian.ext
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.CategoryTheory.Functor.LeftDerived
import Mathbin.CategoryTheory.Linear.Yoneda
import Mathbin.CategoryTheory.Abelian.Opposite
import Mathbin.CategoryTheory.Abelian.Projective

/-!
# Ext

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ Module R` for any `R`-linear abelian category `C`
by (left) deriving in the first argument of the bifunctor `(X, Y) ↦ Module.of R (unop X ⟶ Y)`.

## Implementation

It's not actually necessary here to assume `C` is abelian,
but the hypotheses, involving both `C` and `Cᵒᵖ`, are quite lengthy,
and in practice the abelian case is hopefully enough.

PROJECT: State the alternative definition in terms of
right deriving in the second argument, and show these agree.
-/


noncomputable section

open CategoryTheory

variable (R : Type _) [Ring R] (C : Type _) [Category C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

/- warning: Ext -> ext is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u_1}) [_inst_1 : Ring.{u_1} R] (C : Type.{u_2}) [_inst_2 : CategoryTheory.Category.{u_3, u_2} C] [_inst_3 : CategoryTheory.Abelian.{u_3, u_2} C _inst_2] [_inst_4 : CategoryTheory.Linear.{u_1, u_3, u_2} R (Ring.toSemiring.{u_1} R _inst_1) C _inst_2 (CategoryTheory.Abelian.toPreadditive.{u_3, u_2} C _inst_2 _inst_3)] [_inst_5 : CategoryTheory.EnoughProjectives.{u_3, u_2} C _inst_2], Nat -> (CategoryTheory.Functor.{u_3, max u_2 u_3, u_2, max u_3 u_2 u_1 (succ u_3)} (Opposite.{succ u_2} C) (CategoryTheory.Category.opposite.{u_3, u_2} C _inst_2) (CategoryTheory.Functor.{u_3, u_3, u_2, max u_1 (succ u_3)} C _inst_2 (ModuleCat.{u_3, u_1} R _inst_1) (ModuleCat.moduleCategory.{u_3, u_1} R _inst_1)) (CategoryTheory.Functor.category.{u_3, u_3, u_2, max u_1 (succ u_3)} C _inst_2 (ModuleCat.{u_3, u_1} R _inst_1) (ModuleCat.moduleCategory.{u_3, u_1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u_1}} [_inst_1 : Semiring.{u_1} R] {C : LaurentPolynomial.{u_1} R _inst_1} {_inst_2 : LaurentPolynomial.{u_1} R _inst_1}, (forall (a : Int), Eq.{succ u_1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : Int) => R) a) (FunLike.coe.{succ u_1, 1, succ u_1} (Finsupp.{0, u_1} Int R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R _inst_1))) Int (fun (a : Int) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : Int) => R) a) (Finsupp.funLike.{0, u_1} Int R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R _inst_1))) C a) (FunLike.coe.{succ u_1, 1, succ u_1} (Finsupp.{0, u_1} Int R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R _inst_1))) Int (fun (a : Int) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : Int) => R) a) (Finsupp.funLike.{0, u_1} Int R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R _inst_1))) _inst_2 a)) -> (Eq.{succ u_1} (LaurentPolynomial.{u_1} R _inst_1) C _inst_2)
Case conversion may be inaccurate. Consider using '#align Ext extₓ'. -/
/-- `Ext R C n` is defined by deriving in the first argument of `(X, Y) ↦ Module.of R (unop X ⟶ Y)`
(which is the second argument of `linear_yoneda`).
-/
@[simps obj map]
def ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R :=
  Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      map := fun Y Y' f => (NatTrans.leftDerived ((linearYoneda R C).map f).rightOp n).leftOp
      map_id' := by
        intro X
        ext Y : 2
        dsimp only [nat_trans.id_app, nat_trans.left_op_app, nat_trans.right_op_app,
          functor.left_op_obj, functor.right_op_obj]
        rw [(linear_yoneda R C).map_id, ← unop_id, nat_trans.right_op_id, nat_trans.left_derived_id]
        rfl
      map_comp' := by
        intro X Y Z f g
        rw [(linear_yoneda R C).map_comp, nat_trans.right_op_comp, nat_trans.left_derived_comp]
        rfl }
#align Ext ext

open ZeroObject

/-- If `X : C` is projective and `n : ℕ`, then `Ext^(n + 1) X Y ≅ 0` for any `Y`. -/
def extSuccOfProjective (X Y : C) [Projective X] (n : ℕ) :
    ((ext R C (n + 1)).obj (Opposite.op X)).obj Y ≅ 0 :=
  let E := (((linearYoneda R C).obj Y).rightOp.leftDerivedObjProjectiveSucc n X).unop.symm
  E ≪≫
    { hom := 0
      inv := 0
      hom_inv_id' := by
        let Z : (ModuleCat R)ᵒᵖ := 0
        rw [← (0 : 0 ⟶ Z.unop).unop_op, ← (0 : Z.unop ⟶ 0).unop_op, ← unop_id, ← unop_comp]
        congr 1
        dsimp
        decide }
#align Ext_succ_of_projective extSuccOfProjective


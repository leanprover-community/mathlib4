/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Span

#align_import algebra.category.Module.tannaka from "leanprover-community/mathlib"@"71150516f28d9826c7341f8815b31f7d8770c212"

/-!
# Tannaka duality for rings

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/

universe u

open CategoryTheory

/-- An ingredient of Tannaka duality for rings:
A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.
-/
def ringEquivEndForget₂ (R : Type u) [Ring R] :
    R ≃+* End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGrp.{u})) where
  toFun r :=
    { app := fun M =>
        @AddCommGrp.ofHom M.carrier M.carrier _ _ (DistribMulAction.toAddMonoidHom M r)
      naturality := fun M N f => by
        ext
        exact (f.map_smul _ _).symm }
  invFun φ := φ.app (ModuleCat.of R R) (1 : R)
  left_inv := by
    intro r
    simp
  right_inv := by
    intro φ
    apply NatTrans.ext
    ext M (x : M)
    have w := congr_fun ((forget _).congr_map
      (φ.naturality (ModuleCat.asHomRight (LinearMap.toSpanSingleton R M x)))) (1 : R)
    exact w.symm.trans (congr_arg (φ.app M) (one_smul R x))
  map_add' := by
    intros
    apply NatTrans.ext
    ext
    dsimp
    simp only [AddCommGrp.ofHom_apply, DistribMulAction.toAddMonoidHom_apply, add_smul]
    rfl
  map_mul' := by
    intros
    apply NatTrans.ext
    ext
    dsimp
    simp only [AddCommGrp.ofHom_apply, DistribMulAction.toAddMonoidHom_apply, mul_smul]
    rfl

#align ring_equiv_End_forget₂ ringEquivEndForget₂

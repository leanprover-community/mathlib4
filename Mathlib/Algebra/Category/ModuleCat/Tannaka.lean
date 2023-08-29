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
    R ≃+* End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGroupCat.{u})) where
  toFun r :=
    { app := fun M =>
        @AddCommGroupCat.ofHom M.carrier M.carrier _ _ (DistribMulAction.toAddMonoidHom M r)
      naturality := fun M N f => by
        ext
        -- ⊢ ↑((AdditiveFunctor.of (forget₂ (ModuleCat R) AddCommGroupCat)).obj.map f ≫ ( …
        exact (f.map_smul _ _).symm }
        -- 🎉 no goals
  invFun φ := φ.app (ModuleCat.of R R) (1 : R)
  left_inv := by
    intro r
    -- ⊢ (fun φ => ↑(NatTrans.app φ (ModuleCat.of R R)) 1) ((fun r => NatTrans.mk fun …
    simp
    -- 🎉 no goals
  right_inv := by
    intro φ
    -- ⊢ (fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom (DistribMulAction.toAdd …
    apply NatTrans.ext
    -- ⊢ ((fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom (DistribMulAction.toAd …
    ext M (x : M)
    -- ⊢ ↑(NatTrans.app ((fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom (Distri …
    have w := congr_fun ((forget _).congr_map
      (φ.naturality (ModuleCat.asHomRight (LinearMap.toSpanSingleton R M x)))) (1 : R)
    exact w.symm.trans (congr_arg (φ.app M) (one_smul R x))
    -- 🎉 no goals
  map_add' := by
    intros
    -- ⊢ Equiv.toFun { toFun := fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom ( …
    apply NatTrans.ext
    -- ⊢ (Equiv.toFun { toFun := fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom  …
    ext
    -- ⊢ ↑(NatTrans.app (Equiv.toFun { toFun := fun r => NatTrans.mk fun M => AddComm …
    dsimp
    -- ⊢ (x✝² + y✝) • x✝ = ↑(NatTrans.app ((NatTrans.mk fun M => AddCommGroupCat.ofHo …
    -- ⊢ Equiv.toFun { toFun := fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom ( …
    simp only [AddCommGroupCat.ofHom_apply, DistribMulAction.toAddMonoidHom_apply, add_smul]
    -- ⊢ (Equiv.toFun { toFun := fun r => NatTrans.mk fun M => AddCommGroupCat.ofHom  …
    -- ⊢ x✝² • x✝ + y✝ • x✝ = ↑(NatTrans.app ((NatTrans.mk fun M => AddCommGroupCat.o …
    -- ⊢ ↑(NatTrans.app (Equiv.toFun { toFun := fun r => NatTrans.mk fun M => AddComm …
    rfl
    -- ⊢ (x✝² * y✝) • x✝ = ↑(NatTrans.app ((NatTrans.mk fun M => AddCommGroupCat.ofHo …
    -- 🎉 no goals
    -- ⊢ x✝² • y✝ • x✝ = ↑(NatTrans.app ((NatTrans.mk fun M => AddCommGroupCat.ofHom  …
  map_mul' := by
    -- 🎉 no goals
    intros
    apply NatTrans.ext
    ext
    dsimp
    simp only [AddCommGroupCat.ofHom_apply, DistribMulAction.toAddMonoidHom_apply, mul_smul]
    rfl

#align ring_equiv_End_forget₂ ringEquivEndForget₂

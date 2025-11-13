/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz, Johan Commelin, Joël Riou
-/
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Opposite
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# If `C` is preadditive, `Cᵒᵖ` has a natural preadditive structure.

-/


open Opposite

namespace CategoryTheory

variable (C : Type*) [Category C] [Preadditive C]

instance : Preadditive Cᵒᵖ where
  homGroup X Y := Equiv.addCommGroup (opEquiv X Y)
  add_comp _ _ _ f f' g := Quiver.Hom.unop_inj (Preadditive.comp_add _ _ _ g.unop f.unop f'.unop)
  comp_add _ _ _ f g g' := Quiver.Hom.unop_inj (Preadditive.add_comp _ _ _ g.unop g'.unop f.unop)

instance moduleEndLeft {X Y : C} : Module (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  smul_zero _ := Limits.comp_zero
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp

@[simp]
theorem unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop :=
  rfl

@[simp]
theorem unop_zsmul {X Y : Cᵒᵖ} (k : ℤ) (f : X ⟶ Y) : (k • f).unop = k • f.unop :=
  rfl

@[simp]
theorem unop_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) : (-f).unop = -f.unop :=
  rfl

@[simp]
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op :=
  rfl

@[simp]
theorem op_zsmul {X Y : C} (k : ℤ) (f : X ⟶ Y) : (k • f).op = k • f.op :=
  rfl

@[simp]
theorem op_neg {X Y : C} (f : X ⟶ Y) : (-f).op = -f.op :=
  rfl

variable {C}

/-- `unop` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
def unopHom (X Y : Cᵒᵖ) : (X ⟶ Y) →+ (Opposite.unop Y ⟶ Opposite.unop X) :=
  AddMonoidHom.mk' (fun f => f.unop) fun f g => unop_add _ f g

@[simp]
theorem unop_sum (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.sum f).unop = s.sum fun i => (f i).unop :=
  map_sum (unopHom X Y) _ _

/-- `op` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
def opHom (X Y : C) : (X ⟶ Y) →+ (Opposite.op Y ⟶ Opposite.op X) :=
  AddMonoidHom.mk' (fun f => f.op) fun f g => op_add _ f g

@[simp]
theorem op_sum (X Y : C) {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.sum f).op = s.sum fun i => (f i).op :=
  map_sum (opHom X Y) _ _

/-- `G ⟶ G` and `(End G)ᵐᵒᵖ` are isomorphic as `(End G)ᵐᵒᵖ`-modules. -/
@[simps]
def Preadditive.homSelfLinearEquivEndMulOpposite (G : C) : (G ⟶ G) ≃ₗ[(End G)ᵐᵒᵖ] (End G)ᵐᵒᵖ where
  toFun f := ⟨f⟩
  map_add' := by cat_disch
  map_smul' := by cat_disch
  invFun := fun ⟨f⟩ => f
  left_inv := by cat_disch
  right_inv := by cat_disch

variable {D : Type*} [Category D] [Preadditive D]

instance Functor.op_additive (F : C ⥤ D) [F.Additive] : F.op.Additive where

instance Functor.rightOp_additive (F : Cᵒᵖ ⥤ D) [F.Additive] : F.rightOp.Additive where

instance Functor.leftOp_additive (F : C ⥤ Dᵒᵖ) [F.Additive] : F.leftOp.Additive where

instance Functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive] : F.unop.Additive where

end CategoryTheory

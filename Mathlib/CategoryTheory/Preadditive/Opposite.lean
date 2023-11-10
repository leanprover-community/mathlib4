/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz, Johan Commelin, Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Logic.Equiv.TransferInstance

#align_import category_theory.preadditive.opposite from "leanprover-community/mathlib"@"f8d8465c3c392a93b9ed226956e26dee00975946"

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

instance moduleEndLeft {X : Cᵒᵖ} {Y : C} : Module (End X) (unop X ⟶ Y) where
  smul_add _ _ _ := Preadditive.comp_add _ _ _ _ _ _
  smul_zero _ := Limits.comp_zero
  add_smul _ _ _ := Preadditive.add_comp _ _ _ _ _ _
  zero_smul _ := Limits.zero_comp
#align category_theory.module_End_left CategoryTheory.moduleEndLeft

@[simp]
theorem unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop :=
  rfl
#align category_theory.unop_add CategoryTheory.unop_add

@[simp]
theorem unop_zsmul {X Y : Cᵒᵖ} (k : ℤ) (f : X ⟶ Y) : (k • f).unop = k • f.unop :=
  rfl
#align category_theory.unop_zsmul CategoryTheory.unop_zsmul

@[simp]
theorem unop_neg {X Y : Cᵒᵖ} (f : X ⟶ Y) : (-f).unop = -f.unop :=
  rfl
#align category_theory.unop_neg CategoryTheory.unop_neg

@[simp]
theorem op_add {X Y : C} (f g : X ⟶ Y) : (f + g).op = f.op + g.op :=
  rfl
#align category_theory.op_add CategoryTheory.op_add

@[simp]
theorem op_zsmul {X Y : C} (k : ℤ) (f : X ⟶ Y) : (k • f).op = k • f.op :=
  rfl
#align category_theory.op_zsmul CategoryTheory.op_zsmul

@[simp]
theorem op_neg {X Y : C} (f : X ⟶ Y) : (-f).op = -f.op :=
  rfl
#align category_theory.op_neg CategoryTheory.op_neg

variable {C}

/-- `unop` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
def unopHom (X Y : Cᵒᵖ) : (X ⟶ Y) →+ (Opposite.unop Y ⟶ Opposite.unop X) :=
  AddMonoidHom.mk' (fun f => f.unop) fun f g => unop_add _ f g
#align category_theory.unop_hom CategoryTheory.unopHom

@[simp]
theorem unop_sum (X Y : Cᵒᵖ) {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.sum f).unop = s.sum fun i => (f i).unop :=
  (unopHom X Y).map_sum _ _
#align category_theory.unop_sum CategoryTheory.unop_sum

/-- `op` induces morphisms of monoids on hom groups of a preadditive category -/
@[simps!]
def opHom (X Y : C) : (X ⟶ Y) →+ (Opposite.op Y ⟶ Opposite.op X) :=
  AddMonoidHom.mk' (fun f => f.op) fun f g => op_add _ f g
#align category_theory.op_hom CategoryTheory.opHom

@[simp]
theorem op_sum (X Y : C) {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (s.sum f).op = s.sum fun i => (f i).op :=
  (opHom X Y).map_sum _ _
#align category_theory.op_sum CategoryTheory.op_sum

variable {D : Type*} [Category D] [Preadditive D]

instance Functor.op_additive (F : C ⥤ D) [F.Additive] : F.op.Additive where
#align category_theory.functor.op_additive CategoryTheory.Functor.op_additive

instance Functor.rightOp_additive (F : Cᵒᵖ ⥤ D) [F.Additive] : F.rightOp.Additive where
#align category_theory.functor.right_op_additive CategoryTheory.Functor.rightOp_additive

instance Functor.leftOp_additive (F : C ⥤ Dᵒᵖ) [F.Additive] : F.leftOp.Additive where
#align category_theory.functor.left_op_additive CategoryTheory.Functor.leftOp_additive

instance Functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.Additive] : F.unop.Additive where
#align category_theory.functor.unop_additive CategoryTheory.Functor.unop_additive

end CategoryTheory

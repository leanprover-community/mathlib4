/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# ...

-/

@[expose] public section

universe w t v u u'

namespace CategoryTheory.Limits.FormalCoproduct

open Opposite

variable {C : Type u} [Category.{v} C]

section

variable {A : Type u'} [Category.{v} A]
  [Preadditive A] [HasProducts.{v} A] (F : Cᵒᵖ ⥤ A) (P : A)

@[simps]
def evalOpCoyonedaObjObj : (FormalCoproduct.{v} C)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := .of (∀ (i : X.unop.I), P ⟶ F.obj (op (X.unop.obj i)))
  map f := AddCommGrpCat.ofHom
    { toFun x i := x (f.unop.f i) ≫ F.map (f.unop.φ i).op
      map_zero' := by aesop
      map_add' := by aesop }

set_option backward.isDefEq.respectTransparency false in
noncomputable def evalOpObjCompPreadditiveCoyonedaObjIso :
    (evalOp.{v} C A).obj F ⋙ preadditiveCoyoneda.obj (op P) ≅ evalOpCoyonedaObjObj F P :=
  NatIso.ofComponents (fun X ↦ AddEquiv.toAddCommGrpIso
    { toFun f i := f ≫ Pi.π _ i
      invFun f := Pi.lift f
      left_inv _ := by cat_disch
      right_inv _ := by cat_disch
      map_add' := by cat_disch })

end

variable (C) in
@[simps obj_obj obj_map map_app]
def evalOpAddCommGrpCat :
    (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ (FormalCoproduct.{v} C)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj F :=
    { obj X := .of (∀ (i : X.unop.I), F.obj (op (X.unop.obj i)))
      map f := AddCommGrpCat.ofHom
        { toFun x i := F.map (f.unop.φ i).op (x (f.unop.f i))
          map_zero' := by aesop
          map_add' := by aesop } }
  map f :=
    { app X := AddCommGrpCat.ofHom
        { toFun x i := f.app _ (x i)
          map_zero' := by aesop
          map_add' := by aesop } }

set_option backward.isDefEq.respectTransparency false in
variable (C) in
noncomputable def evalOpAddCommGrpCatIso :
    evalOp.{v} C AddCommGrpCat.{v} ≅ evalOpAddCommGrpCat C :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents (fun _ ↦ AddCommGrpCat.piIso _) (fun f ↦ by
      ext x
      dsimp
      ext i
      rw [AddCommGrpCat.piIso_hom_apply, AddCommGrpCat.piIso_hom_apply,
        ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
      simp)) (fun g ↦ by
    ext X x
    dsimp
    ext i
    rw [AddCommGrpCat.piIso_hom_apply, AddCommGrpCat.piIso_hom_apply,
        ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    simp)

end CategoryTheory.Limits.FormalCoproduct

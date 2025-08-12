/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Opposites

/-!
# Opposites of joins of categories

This file constructs the canonical equivalence of categories `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ`.
The equivalence gets characterized in both directions.

-/

namespace CategoryTheory.Join
open Opposite Functor

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

/-- The equivalence `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ` induced by `Join.opEquivFunctor` and
`Join.opEquivInverse`. -/
def opEquiv : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
  functor := Functor.leftOp <|
    Join.mkFunctor (inclRight _ _).rightOp (inclLeft _ _).rightOp {app _ := (edge _ _).op}
  inverse := Join.mkFunctor (inclRight _ _).op (inclLeft _ _).op {app _ := (edge _ _).op}
  unitIso := NatIso.ofComponents
    (fun
      | op (left _) => Iso.refl _
      | op (right _) => Iso.refl _ )
    (@fun
      | op (left _), op (left _), _ => by cat_disch
      | op (right _), op (left _), _ => by cat_disch
      | op (right _), op (right _), _ => by cat_disch)
  counitIso := NatIso.ofComponents
    (fun
      | left _ => Iso.refl _
      | right _ => Iso.refl _)
  functor_unitIso_comp
    | op (left _) => by cat_disch
    | op (right _) => by cat_disch

variable {C} in
@[simp]
lemma opEquiv_functor_obj_op_left (c : C) :
    (opEquiv C D).functor.obj (op <| left c) = right (op c) :=
  rfl

variable {D} in
@[simp]
lemma opEquiv_functor_obj_op_right (d : D) :
    (opEquiv C D).functor.obj (op <| right d) = left (op d) :=
  rfl

variable {C} in
@[simp]
lemma opEquiv_functor_map_op_inclLeft {c c' : C} (f : c ⟶ c') :
    (opEquiv C D).functor.map (op <| (inclLeft C D).map f) = (inclRight _ _).map (op f) :=
  rfl

variable {D} in
@[simp]
lemma opEquiv_functor_map_op_inclRight {d d' : D} (f : d ⟶ d') :
    (opEquiv C D).functor.map (op <| (inclRight C D).map f) = (inclLeft _ _).map (op f) :=
  rfl

variable {C D} in
lemma opEquiv_functor_map_op_edge (c : C) (d : D) :
    (opEquiv C D).functor.map (op <| edge c d) = edge (op d) (op c) :=
  rfl

/-- Characterize (up to a rightOp) the action of the left inclusion on `Join.opEquivFunctor`. -/
@[simps!]
def InclLeftCompRightOpOpEquivFunctor :
    inclLeft C D ⋙ (opEquiv C D).functor.rightOp ≅ (inclRight _ _).rightOp :=
  isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorLeft _ _ _

/-- Characterize (up to a rightOp) the action of the right inclusion on `Join.opEquivFunctor`. -/
@[simps!]
def InclRightCompRightOpOpEquivFunctor :
    inclRight C D ⋙ (opEquiv C D).functor.rightOp ≅ (inclLeft _ _).rightOp :=
  isoWhiskerLeft _ (leftOpRightOpIso _) ≪≫ mkFunctorRight _ _ _

variable {D} in
@[simp]
lemma opEquiv_inverse_obj_left_op (d : D) :
    (opEquiv C D).inverse.obj (left <| op d) = op (right d) :=
  rfl

variable {C} in
@[simp]
lemma opEquiv_inverse_obj_right_op (c : C) :
    (opEquiv C D).inverse.obj (right <| op c) = op (left c) :=
  rfl

variable {D} in
@[simp]
lemma opEquiv_inverse_map_inclLeft_op {d d' : D} (f : d ⟶ d') :
    (opEquiv C D).inverse.map ((inclLeft Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclRight _ _).map f) :=
  rfl

variable {D} in
@[simp]
lemma opEquiv_inverse_map_inclRight_op {c c' : C} (f : c ⟶ c') :
    (opEquiv C D).inverse.map ((inclRight Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclLeft _ _).map f) :=
  rfl

variable {C D} in
@[simp]
lemma opEquiv_inverse_map_edge_op (c : C) (d : D) :
    (opEquiv C D).inverse.map (edge (op d) (op c)) = op (edge c d) :=
  rfl

/-- Characterize `Join.opEquivInverse` with respect to the left inclusion -/
def inclLeftCompOpEquivInverse :
    Join.inclLeft Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse ≅ (inclRight _ _).op :=
  Join.mkFunctorLeft _ _ _

/-- Characterize `Join.opEquivInverse` with respect to the right inclusion -/
def inclRightCompOpEquivInverse :
    Join.inclRight Dᵒᵖ Cᵒᵖ ⋙ (opEquiv C D).inverse ≅ (inclLeft _ _).op :=
  Join.mkFunctorRight _ _ _

variable {D} in
@[simp]
lemma inclLeftCompOpEquivInverse_hom_app_op (d : D) :
    (inclLeftCompOpEquivInverse C D).hom.app (op d) = 𝟙 (op <| right d) :=
  rfl

variable {C} in
@[simp]
lemma inclRightCompOpEquivInverse_hom_app_op (c : C) :
    (inclRightCompOpEquivInverse C D).hom.app (op c) = 𝟙 (op <| left c) :=
  rfl

variable {D} in
@[simp]
lemma inclLeftCompOpEquivInverse_inv_app_op (d : D) :
    (inclLeftCompOpEquivInverse C D).inv.app (op d) = 𝟙 (op <| right d) :=
  rfl

variable {C} in
@[simp]
lemma inclRightCompOpEquivInverse_inv_app_op (c : C) :
    (inclRightCompOpEquivInverse C D).inv.app (op c) = 𝟙 (op <| left c) :=
  rfl

end CategoryTheory.Join

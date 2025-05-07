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
open Opposite

variable (C D : Type*) [Category C] [Category D]

/-- The forward direction of `Join.opEquiv`. -/
def opEquivFunctor : (C ⋆ D)ᵒᵖ ⥤ Dᵒᵖ ⋆ Cᵒᵖ :=
  Functor.leftOp <|
    Join.mkFunctor (inclRight _ _).rightOp (inclLeft _ _).rightOp ({app _ := (edge _ _).op})

variable {C} in
@[simp]
lemma opEquivFunctor_obj_op_left (c : C) :
    (opEquivFunctor C D).obj (op <| left c) = right (op c) :=
  rfl

variable {D} in
@[simp]
lemma opEquivFunctor_obj_op_right (d : D) :
    (opEquivFunctor C D).obj (op <| right d) = left (op d) :=
  rfl

variable {C} in
@[simp]
lemma opEquivFunctor_map_op_inclLeft {c c' : C} (f : c ⟶ c') :
    (opEquivFunctor C D).map (op <| (inclLeft C D).map f) = (inclRight _ _).map (op f) :=
  rfl

variable {D} in
@[simp]
lemma opEquivFunctor_map_op_inclRight {d d' : D} (f : d ⟶ d') :
    (opEquivFunctor C D).map (op <| (inclRight C D).map f) = (inclLeft _ _).map (op f) :=
  rfl

variable {C D} in
lemma opEquivFunctor_map_op_edge (c : C) (d : D) :
    (opEquivFunctor C D).map (op <| edge c d) = edge (op d) (op c) :=
  rfl

/-- Characterize (up to a rightOp) the action of the left inclusion on `Join.opEquivFunctor`. -/
@[simps!]
def rightOpOpEquivFunctorCompInclLeft :
    inclLeft C D ⋙ (opEquivFunctor C D).rightOp ≅ (inclRight _ _).rightOp :=
  isoWhiskerLeft _ (Functor.leftOpRightOpIso _) ≪≫ mkFunctorLeft _ _ _

/-- Characterize (up to a rightOp) the action of the right inclusion on `Join.opEquivFunctor`. -/
@[simps!]
def rightOpOpEquivFunctorCompInclRight :
    inclRight C D ⋙ (opEquivFunctor C D).rightOp ≅ (inclLeft _ _).rightOp :=
  isoWhiskerLeft _ (Functor.leftOpRightOpIso _) ≪≫ mkFunctorRight _ _ _

/-- The backward direction of `Join.opEquiv`. -/
def opEquivInverse : Dᵒᵖ ⋆ Cᵒᵖ ⥤ (C ⋆ D)ᵒᵖ :=
    Join.mkFunctor (inclRight _ _).op (inclLeft _ _).op ({app _ := (edge _ _).op})

variable {D} in
@[simp]
lemma opEquivInverse_obj_left_op (d : D) :
    (opEquivInverse C D).obj (left <| op d) = op (right d) :=
  rfl

variable {C} in
@[simp]
lemma opEquivInverse_obj_right_op (c : C) :
    (opEquivInverse C D).obj (right <| op c) = op (left c) :=
  rfl

variable {D} in
@[simp]
lemma opEquivInverse_map_inclLeft_op {d d' : D} (f : d ⟶ d') :
    (opEquivInverse C D).map ((inclLeft Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclRight _ _).map f) :=
  rfl

variable {D} in
@[simp]
lemma opEquivInverse_map_inclRight_op {c c' : C} (f : c ⟶ c') :
    (opEquivInverse C D).map ((inclRight Dᵒᵖ Cᵒᵖ).map f.op) = op ((inclLeft _ _).map f) :=
  rfl

variable {C D} in
@[simp]
lemma opEquivInverse_map_edge_op (c : C) (d : D) :
    (opEquivInverse C D).map (edge (op d) (op c)) = op (edge c d) :=
  rfl

/-- Characterize `Join.opEquivInverse` with respect to the left inclusion -/
def opEquivInverseCompInclLeft :
    (Join.inclLeft Dᵒᵖ Cᵒᵖ) ⋙ opEquivInverse C D ≅ (inclRight _ _).op :=
  Join.mkFunctorLeft _ _ _

/-- Characterize `Join.opEquivInverse` with respect to the right inclusion -/
def opEquivInverseCompInclRight :
    (Join.inclRight Dᵒᵖ Cᵒᵖ) ⋙ opEquivInverse C D ≅ (inclLeft _ _).op :=
  Join.mkFunctorRight _ _ _

variable {D} in
@[simp]
lemma opEquivInverseCompInclLeft_hom_app_op (d : D) :
    (opEquivInverseCompInclLeft C D).hom.app (op d) = 𝟙 (op <| right d) :=
  rfl

variable {C} in
@[simp]
lemma opEquivInverseCompInclRight_hom_app_op (c : C) :
    (opEquivInverseCompInclRight C D).hom.app (op c) = 𝟙 (op <| left c) :=
  rfl

variable {D} in
@[simp]
lemma opEquivInverseCompInclLeft_inv_app_op (d : D) :
    (opEquivInverseCompInclLeft C D).inv.app (op d) = 𝟙 (op <| right d) :=
  rfl

variable {C} in
@[simp]
lemma opEquivInverseCompInclRight_inv_app_op (c : C) :
    (opEquivInverseCompInclRight C D).inv.app (op c) = 𝟙 (op <| left c) :=
  rfl

/-- The equivalence `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ` induced by `Join.opEquivFunctor` and
`Join.opEquivInverse`. -/
def opEquiv : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
  functor := opEquivFunctor C D
  inverse := opEquivInverse C D
  unitIso := NatIso.ofComponents
    (fun ⟨x⟩ ↦ match x with
      | left _ => Iso.refl _
      | right _ => Iso.refl _ )
    (fun {x y} f ↦ match x, y, f with
      | op (left _), op (left _), _ => by aesop_cat
      | op (right _), op (left _), _ => by aesop_cat
      | op (right _), op (right _), _ => by aesop_cat)
  counitIso := NatIso.ofComponents
    (fun x ↦ match x with
      | left _ => Iso.refl _
      | right _ => Iso.refl _ )
  functor_unitIso_comp
    | op (left _) => by aesop_cat
    | op (right _) => by aesop_cat

end CategoryTheory.Join

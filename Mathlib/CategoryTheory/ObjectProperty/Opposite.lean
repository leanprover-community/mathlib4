/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Opposites

/-!
# Opposite of a property of objects

-/

namespace CategoryTheory

open Opposite

variable {C : Type*} [Category C]

namespace ObjectProperty

protected def op (P : ObjectProperty C) : ObjectProperty Cᵒᵖ := fun X ↦ P X.unop
protected def unop (P : ObjectProperty Cᵒᵖ) : ObjectProperty C := fun X ↦ P (op X)
@[simp] lemma prop_op_iff (P : ObjectProperty C) (X : Cᵒᵖ) : P.op X ↔ P X.unop := Iff.rfl
@[simp] lemma prop_unop_iff (P : ObjectProperty Cᵒᵖ) (X : C) : P.unop X ↔ P (op X) := Iff.rfl
@[simp] lemma op_unop (P : ObjectProperty Cᵒᵖ) : P.unop.op = P := rfl
@[simp] lemma unop_op (P : ObjectProperty C) : P.op.unop = P := rfl

instance (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] :
    P.op.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_iso e.symm.unop

instance (P : ObjectProperty Cᵒᵖ) [P.IsClosedUnderIsomorphisms] :
    P.unop.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_iso e.symm.op

end ObjectProperty

end CategoryTheory

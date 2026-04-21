/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!

# Representable functors in concrete categories

This file provides some API for the situation `(F ⋙ forget D).RepresentableBy Y`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Functor.RepresentableBy

open Opposite

variable {C D : Type*} [Category* C] [Category* D] {F : Cᵒᵖ ⥤ D}
    {CD : D → Type*} {FD : D → D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] {Y : C} (α : (F ⋙ forget D).RepresentableBy Y)

/-- The natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
def homEquiv' {X : C} : (X ⟶ Y) ≃ ToType (F.obj (op X)) := α.homEquiv

lemma homEquiv'_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    α.homEquiv' (f ≫ g) = F.map f.op (α.homEquiv' g) := α.homEquiv_comp _ _

end CategoryTheory.Functor.RepresentableBy

/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
In this file we provide various simp lemmas in its elementwise form via `Tactic.Elementwise`.
-/

public section


open CategoryTheory CategoryTheory.Limits

attribute [elementwise (attr := simp)] Cone.w limit.lift_π limit.w
  colimit.ι_desc colimit.w kernel.lift_ι cokernel.π_desc kernel.condition cokernel.condition

attribute [elementwise] Cocone.w

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {F : C ⥤ Type*}

@[simp]
lemma Cocone.w_apply' (c : Cocone F) {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    c.ι.app Y (F.map f x) = c.ι.app X x :=
  c.w_apply f x

@[simp]
lemma Cone.w_apply' (c : Cone F) {X Y : C} (f : X ⟶ Y) (x : c.pt) :
    (F.map f) (c.π.app X x) = c.π.app Y x :=
  c.w_apply f x

end CategoryTheory.Limits

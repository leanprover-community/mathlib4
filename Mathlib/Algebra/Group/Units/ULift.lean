/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Results about `Units` and `ULift`
-/

public section

universe u v

variable {M : Type u} [Monoid M]

namespace ULift

@[to_additive (attr := simp)]
theorem isUnit_up {a : M} : IsUnit (ULift.up.{v} a) ↔ IsUnit a :=
  ⟨IsUnit.map MulEquiv.ulift, IsUnit.map MulEquiv.ulift.symm⟩

@[to_additive (attr := simp)]
theorem isUnit_down {a : ULift.{v} M} : IsUnit a.down ↔ IsUnit a :=
  ULift.isUnit_up.symm

end ULift

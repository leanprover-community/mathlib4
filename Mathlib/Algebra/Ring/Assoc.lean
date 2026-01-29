/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Hom.End

universe u

variable (R : Type u) [NonUnitalNonAssocSemiring R]

namespace AddMonoidHom

def mull₃ : R →+ R →+ R →+ R where
  toFun x := comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' := fun x y => by ext; simp [add_mul]

@[simp]
theorem mull₃_apply (x y z : R) : mull₃ R x y z = (x * y) * z := by simp [mull₃]

def mulr₃ : R →+ R →+ R →+ R where
  toFun x := compr₂ mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' := fun x y => by ext; simp [add_mul]

@[simp]
theorem mulr₃_apply (x y z : R) : mulr₃ R x y z = x * (y * z) := by simp [mulr₃]

theorem associative_iff_mull₃_eq_mulr₃ : (∀ (x y z : R), (x * y) * z = x * (y * z)) ↔
  mull₃ R = mulr₃ R := by
  constructor
  · intro h
    ext x y z
    simp [h x y z]
  · intro h x y z
    rw [← mull₃_apply, ← mulr₃_apply, h]


end AddMonoidHom

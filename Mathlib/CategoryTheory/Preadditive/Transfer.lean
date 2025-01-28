/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Equiv.TransferInstance

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} (hF : F.FullyFaithful)

@[simp]
lemma Functor.FullyFaithful.preimage_comp {P Q R : C} (f : F.obj P ⟶ F.obj Q)
    (g : F.obj Q ⟶ F.obj R) :  hF.preimage (f ≫ g) = hF.preimage f ≫ hF.preimage g := by
  apply hF.map_injective
  rw [F.map_comp]
  simp

def Functor.FullyFaithful.pullback_preadditive [Preadditive D] : Preadditive C where
  homGroup P Q := hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

end CategoryTheory

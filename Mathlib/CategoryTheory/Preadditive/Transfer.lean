/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Equiv.TransferInstance

/-!
# Pulling back a preadditive structure along a fully faithful functor

A preadditive structure on a category `D` transfers to a preadditive structure on `C` for a given
fully faithful functor `F : C ⥤ D`.
-/
namespace CategoryTheory.Preadditive

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable {F : C ⥤ D} (hF : F.FullyFaithful)

/-- If `D` is a preadditive category, any fully faithful functor `F : C ⥤ D` induces a preadditive
structure on `C`. -/
def ofFullyFaithful : Preadditive C where
  homGroup P Q := hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

instance additive_ofFullyFaithful :
    letI : Preadditive C := ofFullyFaithful hF
    F.Additive :=
  letI : Preadditive C := ofFullyFaithful hF
  { map_add := by simp [Equiv.add_def] }

end CategoryTheory.Preadditive

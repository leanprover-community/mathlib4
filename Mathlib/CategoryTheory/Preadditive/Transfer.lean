/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Pulling back a preadditive structure along a fully faithful functor

A preadditive structure on a category `D` transfers to a preadditive structure on `C` for a given
fully faithful functor `F : C ⥤ D`.
-/
namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable {F : C ⥤ D} (hF : F.FullyFaithful)

namespace Preadditive


/-- If `D` is a preadditive category, any fully faithful functor `F : C ⥤ D` induces a preadditive
structure on `C`. -/
def ofFullyFaithful : Preadditive C where
  homGroup P Q := hF.homEquiv.addCommGroup
  add_comp P Q R f f' g := hF.map_injective (by simp [Equiv.add_def])
  comp_add P Q R f g g' := hF.map_injective (by simp [Equiv.add_def])

end Preadditive

open Preadditive
namespace Functor.FullyFaithful

/-- The preadditive structure on `C` induced by a fully faithful functor `F : C ⥤ D` makes `F` an
additive functor. -/
lemma additive_ofFullyFaithful :
    letI : Preadditive C := Preadditive.ofFullyFaithful hF
    F.Additive :=
  letI : Preadditive C := Preadditive.ofFullyFaithful hF
  { map_add := by simp [Equiv.add_def] }

end Functor.FullyFaithful

namespace Equivalence

/-- The preadditive structure on `C` induced by an equivalence `e : C ≌ D` makes `e.inverse` an
additive functor. -/
lemma additive_inverse_of_FullyFaithful (e : C ≌ D) :
    letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
    e.inverse.Additive :=
  letI : Preadditive C := ofFullyFaithful e.fullyFaithfulFunctor
  letI : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  e.inverse_additive

end Equivalence

end CategoryTheory

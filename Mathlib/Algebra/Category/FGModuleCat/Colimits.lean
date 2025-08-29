/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# `forget₂ (FGModuleCat K) (ModuleCat K)` creates all finite colimits.

And hence `FGModuleCat K` has all finite colimits.

-/

noncomputable section

universe v u

open CategoryTheory Limits

namespace FGModuleCat

variable {J : Type} [SmallCategory J] [FinCategory J] {k : Type u} [Ring k]

instance {J : Type} [Finite J] (Z : J → ModuleCat.{v} k) [∀ j, Module.Finite k (Z j)] :
    Module.Finite k (∐ fun j => Z j : ModuleCat.{v} k) := by
  classical
exact (Module.Finite.equiv_iff (ModuleCat.coprodIsoDirectSum Z).toLinearEquiv).mpr inferInstance

/-- Finite colimits of finite modules are finite, because we can realise them as quotients
of a finite coproduct. -/
instance (F : J ⥤ FGModuleCat k) :
    Module.Finite k (colimit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
have (j : J) : Module.Finite k ((F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)).obj j) := by
    change Module.Finite k (F.obj j); infer_instance
  Module.Finite.of_surjective
    (colimitQuotientCoproduct (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k))).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat k` to `ModuleCat k` creates all finite colimits. -/
def forget₂CreatesColimit (F : J ⥤ FGModuleCat k) :
    CreatesColimit F (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) :=
  createsColimitOfFullyFaithfulOfIso
    ⟨(colimit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

instance : CreatesColimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  CreatesColimit {F} := forget₂CreatesColimit F

instance (J : Type) [Category J] [FinCategory J] :
    HasColimitsOfShape J (FGModuleCat.{v} k) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (forget₂ (FGModuleCat k) (ModuleCat.{v} k))

instance : HasFiniteColimits (FGModuleCat.{v} k) where
  out _ _ _ := inferInstance

instance : PreservesFiniteColimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  preservesFiniteColimits _ _ _ := inferInstance

end FGModuleCat

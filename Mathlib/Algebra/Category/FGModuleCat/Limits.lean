/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# `forget₂ (FGModuleCat K) (ModuleCat K)` creates all finite limits.

And hence `FGModuleCat K` has all finite limits.

## Future work
After generalising `FGModuleCat` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.

Analogous constructions for Noetherian modules.
-/

noncomputable section

universe v u

open CategoryTheory Limits

namespace FGModuleCat

variable {J : Type} [SmallCategory J] [FinCategory J]
variable {k : Type u} [Ring k]

instance {J : Type} [Finite J] (Z : J → ModuleCat.{v} k) [∀ j, Module.Finite k (Z j)] :
    Module.Finite k (∏ᶜ fun j => Z j : ModuleCat.{v} k) :=
  haveI : Module.Finite k (ModuleCat.of k (∀ j, Z j)) := by unfold ModuleCat.of; infer_instance
  (Module.Finite.equiv_iff (ModuleCat.piIsoPi Z).toLinearEquiv).mpr inferInstance

variable [IsNoetherianRing k]

/-- Finite limits of finite-dimensional vector spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FGModuleCat k) :
    Module.Finite k (limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  haveI : ∀ j, Module.Finite k ((F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)).obj j) := by
    intro j; change Module.Finite k (F.obj j); infer_instance
  Module.Finite.of_injective
    (limitSubobjectProduct (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k))).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat k` to `ModuleCat k` creates all finite limits. -/
def forget₂CreatesLimit (F : J ⥤ FGModuleCat k) :
    CreatesLimit F (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k),
      by rw [ModuleCat.isFG_iff]; infer_instance⟩
    (Iso.refl _)

instance : CreatesLimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  CreatesLimit {F} := forget₂CreatesLimit F

instance (J : Type) [Category J] [FinCategory J] :
    HasLimitsOfShape J (FGModuleCat.{v} k) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (forget₂ (FGModuleCat k) (ModuleCat.{v} k))

instance : HasFiniteLimits (FGModuleCat.{v} k) where
  out _ _ _ := inferInstance

instance : PreservesFiniteLimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  preservesFiniteLimits _ _ _ := inferInstance

end FGModuleCat

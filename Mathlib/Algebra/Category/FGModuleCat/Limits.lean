/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

#align_import algebra.category.fgModule.limits from "leanprover-community/mathlib"@"19a70dceb9dff0994b92d2dd049de7d84d28112b"

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

open CategoryTheory

open CategoryTheory.Limits

namespace FGModuleCat

variable {J : Type} [SmallCategory J] [FinCategory J]

variable {k : Type v} [Field k]

instance {J : Type} [Fintype J] (Z : J → ModuleCat.{v} k) [∀ j, FiniteDimensional k (Z j)] :
    FiniteDimensional k (∏ fun j => Z j : ModuleCat.{v} k) :=
  haveI : FiniteDimensional k (ModuleCat.of k (∀ j, Z j)) := by unfold ModuleCat.of; infer_instance
                                                                -- ⊢ FiniteDimensional k ↑(ModuleCat.mk ((j : J) → ↑(Z j)))
                                                                                     -- 🎉 no goals
  FiniteDimensional.of_injective (ModuleCat.piIsoPi _).hom
    ((ModuleCat.mono_iff_injective _).1 (by infer_instance))
                                            -- 🎉 no goals

/-- Finite limits of finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FGModuleCat k) :
    FiniteDimensional k (limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  haveI : ∀ j, FiniteDimensional k ((F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)).obj j) := by
    intro j; change FiniteDimensional k (F.obj j); infer_instance
    -- ⊢ FiniteDimensional k ↑((F ⋙ forget₂ (FGModuleCat k) (ModuleCat k)).obj j)
             -- ⊢ FiniteDimensional k ↑(F.obj j)
                                                   -- 🎉 no goals
  FiniteDimensional.of_injective
    (limitSubobjectProduct (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)))
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat k` to `ModuleCat k` creates all finite limits. -/
def forget₂CreatesLimit (F : J ⥤ FGModuleCat k) :
    CreatesLimit F (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k), inferInstance⟩
    (Iso.refl _)
set_option linter.uppercaseLean3 false in
#align fgModule.forget₂_creates_limit FGModuleCat.forget₂CreatesLimit

instance : CreatesLimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  CreatesLimit {F} := forget₂CreatesLimit F

instance : HasFiniteLimits (FGModuleCat k) where
  out _ _ _ := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (forget₂ (FGModuleCat k) (ModuleCat.{v} k))

instance : PreservesFiniteLimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  preservesFiniteLimits _ _ _ := inferInstance

end FGModuleCat

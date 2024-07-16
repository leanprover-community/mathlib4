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

variable {R : Type v} [Ring R] [IsNoetherianRing R]

instance {J : Type} [Finite J] (Z : J → ModuleCat.{v} k) [∀ j, FiniteDimensional k (Z j)] :
    FiniteDimensional k (∏ᶜ fun j => Z j : ModuleCat.{v} k) :=
  haveI : FiniteDimensional k (ModuleCat.of k (∀ j, Z j)) := by unfold ModuleCat.of; infer_instance
  FiniteDimensional.of_injective (ModuleCat.piIsoPi _).hom
    ((ModuleCat.mono_iff_injective _).1 (by infer_instance))

instance {J : Type} [Finite J] (Z : J → ModuleCat R) [∀ j, Module.Finite R (Z j)] :
    Module.Finite R (∏ fun j => Z j : ModuleCat R) :=
  haveI : Module.Finite R (ModuleCat.of R (∀ j, Z j)) := by unfold ModuleCat.of; infer_instance
  Module.Finite.of_injective (ModuleCat.piIsoPi _).hom
    ((ModuleCat.mono_iff_injective _).1 (by infer_instance))

/-- Finite limits of finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FGModuleCat k) :
    FiniteDimensional k (limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  haveI : ∀ j, FiniteDimensional k ((F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)).obj j) := by
    intro j; change FiniteDimensional k (F.obj j); infer_instance
  FiniteDimensional.of_injective
    (limitSubobjectProduct (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)))
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

instance (F : J ⥤ FGModuleCat R) :
    Module.Finite R (limit (F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)) : ModuleCat.{v} R) :=
  haveI : ∀ j, Module.Finite R ((F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)).obj j) := by
    intro j; change Module.Finite R (F.obj j); infer_instance
  Module.Finite.of_injective
    (limitSubobjectProduct (F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)))
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The forgetful functor from `FGModuleCat k` to `ModuleCat k` creates all finite limits. -/
def forget₂CreatesLimit (F : J ⥤ FGModuleCat k) :
    CreatesLimit F (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k), inferInstance⟩
    (Iso.refl _)
set_option linter.uppercaseLean3 false in
#align fgModule.forget₂_creates_limit FGModuleCat.forget₂CreatesLimit

/-- The forgetful functor from `FGModuleCat R` to `ModuleCat R` creates all finite limits when `R`
is Noetherian. -/
def forget₂CreatesLimitOfNoetherian (F : J ⥤ FGModuleCat R) :
    CreatesLimit F (forget₂ (FGModuleCat R) (ModuleCat.{v} R)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FGModuleCat R) (ModuleCat.{v} R)) : ModuleCat.{v} R), inferInstance⟩
    (Iso.refl _)

instance : CreatesLimitsOfShape J (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  CreatesLimit {F} := forget₂CreatesLimit F

instance : CreatesLimitsOfShape J (forget₂ (FGModuleCat R) (ModuleCat.{v} R)) where
  CreatesLimit {F} := forget₂CreatesLimitOfNoetherian F

instance (J : Type) [Category J] [FinCategory J] :
    HasLimitsOfShape J (FGModuleCat.{v} k) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (forget₂ (FGModuleCat k) (ModuleCat.{v} k))

instance (J : Type) [Category J] [FinCategory J] :
    HasLimitsOfShape J (FGModuleCat.{v} R) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (forget₂ (FGModuleCat R) (ModuleCat.{v} R))

instance : HasFiniteLimits (FGModuleCat k) where
  out _ _ _ := inferInstance

instance : HasFiniteLimits (FGModuleCat R) where
  out _ _ _ := inferInstance

instance : PreservesFiniteLimits (forget₂ (FGModuleCat k) (ModuleCat.{v} k)) where
  preservesFiniteLimits _ _ _ := inferInstance

instance : PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat.{v} R)) where
  preservesFiniteLimits _ _ _ := inferInstance

end FGModuleCat

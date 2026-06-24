/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The full subcategory of injective objects

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable (C : Type u) [Category.{v} C]

/-- The full subcategory of injective objects in a category `C`. -/
abbrev InjectiveObject : Type u := ObjectProperty.FullSubcategory (isInjective C)

namespace InjectiveObject

instance closedUnderLimitsOfShapeDiscrete (J : Type*) :
    ObjectProperty.IsClosedUnderLimitsOfShape (isInjective C) (Discrete J) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have : HasLimit p.diag := ⟨_, p.isLimit⟩
    let X := fun j => p.diag.obj ⟨j⟩
    let e := Discrete.natIsoFunctor (F := p.diag)
    have : HasProduct X := hasLimit_of_iso e
    have : HasLimit (Discrete.functor (p.diag.obj ∘ Discrete.mk)) := by
      change HasProduct X
      infer_instance
    have : ∀ j, Injective (X j) := fun j => p.prop_diag_obj ⟨j⟩
    have e' : ∏ᶜ X ≅ Y := IsLimit.conePointUniqueUpToIso (limit.isLimit _)
      ((IsLimit.postcomposeHomEquiv e _).symm p.isLimit)
    exact Injective.of_iso e' inferInstance

instance [HasFiniteProducts C] : HasFiniteProducts (InjectiveObject C) where
  out n := by infer_instance

instance [Preadditive C] [HasFiniteProducts C] : HasFiniteBiproducts (InjectiveObject C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance [HasZeroMorphisms C] [HasZeroObject C] : (isInjective C).ContainsZero where
  exists_zero := ⟨0, by simp [IsZero.iff_id_eq_zero], Injective.zero_injective⟩

instance [HasZeroMorphisms C] [HasZeroObject C] : HasZeroObject (InjectiveObject C) := inferInstance

/-- The inclusion `InjectiveObject C ⥤ C` of the full subcategory of
injective objects in `C`. -/
abbrev ι : InjectiveObject C ⥤ C := ObjectProperty.ι _

instance (X : InjectiveObject C) : Injective ((ι C).obj X) := X.2

instance (X : InjectiveObject C) : Injective X.obj := X.2

end InjectiveObject

end CategoryTheory

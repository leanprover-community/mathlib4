/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Generator.Type

/-!
# The category of types is locally presentable

-/

universe u

namespace CategoryTheory.Types

open Opposite Limits

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

instance : IsCardinalPresentable PUnit.{u + 1} κ where
  preservesColimitOfShape J _ _ := by
    let e : coyoneda.obj (op (PUnit.{u + 1})) ≅ 𝟭 _ :=
      NatIso.ofComponents (fun X ↦ Equiv.toIso
        { toFun f := f .unit
          invFun x _ := x })
    exact preservesColimitsOfShape_of_natIso e.symm

lemma isStrongGenerator_punit :
    (ObjectProperty.singleton (PUnit.{u + 1})).IsStrongGenerator  := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨isSeparator_punit, fun _ _ i hi₁ hi₂ ↦ ?_⟩
  · rw [mono_iff_injective] at hi₁
    rw [isIso_iff_bijective]
    refine ⟨hi₁, fun y ↦ ?_⟩
    obtain ⟨f, hf⟩ := hi₂ PUnit ⟨.unit⟩ (fun _ ↦ y)
    exact ⟨f .unit, congr_fun hf .unit⟩

instance : IsCardinalLocallyPresentable (Type u) κ := by
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  exact ⟨.singleton PUnit, inferInstance, isStrongGenerator_punit,
    by simp [isCardinalPresentable_iff]; infer_instance⟩

instance : IsLocallyPresentable.{u} (Type u) where
  exists_cardinal := ⟨_, Cardinal.fact_isRegular_aleph0, inferInstance⟩

end CategoryTheory.Types

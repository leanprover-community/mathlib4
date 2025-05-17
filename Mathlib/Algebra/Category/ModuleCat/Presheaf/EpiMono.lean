/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits

/-!
# Epimorphisms and monomorphisms in the category of presheaves of modules

In this file, we give characterizations of epimorphisms and monomorphisms
in the category of presheaves of modules.

-/

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

lemma epi_of_surjective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where
  left_cancellation g₁ g₂ hg := by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact congr_fun ((evaluation R X ⋙ forget _).congr_map hg) m₁

lemma mono_of_injective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where
  right_cancellation {M} g₁ g₂ hg := by
    ext X m
    exact hf (congr_fun ((evaluation R X ⋙ forget _).congr_map hg) m)

variable (f)

instance [Epi f] (X : Cᵒᵖ) : Epi (f.app X) :=
  inferInstanceAs (Epi ((evaluation R X).map f))

instance [Mono f] (X : Cᵒᵖ) : Mono (f.app X) :=
  inferInstanceAs (Mono ((evaluation R X).map f))

lemma surjective_of_epi [Epi f] (X : Cᵒᵖ) :
    Function.Surjective (f.app X) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

lemma injective_of_mono [Mono f] (X : Cᵒᵖ) :
    Function.Injective (f.app X) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

lemma epi_iff_surjective :
    Epi f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X) :=
  ⟨fun _ ↦ surjective_of_epi f, epi_of_surjective⟩

lemma mono_iff_surjective :
    Mono f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X) :=
  ⟨fun _ ↦ injective_of_mono f, mono_of_injective⟩

end PresheafOfModules

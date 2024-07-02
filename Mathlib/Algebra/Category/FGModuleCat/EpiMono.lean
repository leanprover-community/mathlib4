/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.Category.FGModuleCat.Basic

/-!
# Monomorphisms in finitely generated modules over a Noetherian ring

This file is almost a copy of `Algebra/ModuleCat/EpiMono.lean`
-/


universe u

open CategoryTheory

namespace FGModuleCat

variable {R : Type u} [Ring R] [IsNoetherianRing R] {X Y : FGModuleCat R} (f : X ⟶ Y)

variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v h =>
    cancel_mono (Z := .of R (LinearMap.ker f)) f |>.1 <| ConcreteCategory.hom_ext _ _ <| by
      rintro ⟨x, hx⟩
      exact LinearMap.congr_fun h ⟨x, hx⟩

theorem range_eq_top_of_epi [Epi f] : LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v h =>
    cancel_epi (Z := .of R (Y ⧸ LinearMap.range f)) f |>.1 <| ConcreteCategory.hom_ext _ _ <| by
      intro x; exact LinearMap.congr_fun h x

theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f = ⊥ :=
  ⟨fun hf => ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert LinearMap.ker_eq_bot.1 hf⟩

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]

theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| LinearMap.range_eq_top (f := (f : X →ₗ[R] Y)) |>.1 hf⟩

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]

/-- If the zero morphism is an epi then the codomain is trivial. -/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((FGModuleCat.epi_iff_surjective _).mp h)

-- instance mono_as_hom'_subtype (U : Submodule R X) : Mono (ModuleCat.asHomRight U.subtype) :=
--   (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)

-- instance epi_as_hom''_mkQ (U : Submodule R X) : Epi (↿U.mkQ) :=
--   (epi_iff_range_eq_top _).mpr <| Submodule.range_mkQ _

instance forget_preservesEpimorphisms : (forget (FGModuleCat R)).PreservesEpimorphisms where
    preserves f hf := by
      erw [CategoryTheory.epi_iff_surjective, ← epi_iff_surjective]
      exact hf

instance forget_preservesMonomorphisms : (forget (FGModuleCat R)).PreservesMonomorphisms where
    preserves f hf := by
      erw [CategoryTheory.mono_iff_injective, ← mono_iff_injective]
      exact hf

end FGModuleCat

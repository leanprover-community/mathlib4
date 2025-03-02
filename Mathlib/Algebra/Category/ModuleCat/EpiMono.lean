/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Monomorphisms in `Module R`

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/


universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

theorem range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert LinearMap.ker_eq_bot.1 hf⟩

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]

theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| by convert LinearMap.range_eq_top.1 hf⟩

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]

/-- If the zero morphism is an epi then the codomain is trivial. -/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)

instance mono_as_hom'_subtype (U : Submodule R X) : Mono (ModuleCat.ofHom U.subtype) :=
  (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)

instance epi_as_hom''_mkQ (U : Submodule R X) : Epi (ModuleCat.ofHom U.mkQ) :=
  (epi_iff_range_eq_top _).mpr <| Submodule.range_mkQ _

instance forget_preservesEpimorphisms : (forget (ModuleCat.{v} R)).PreservesEpimorphisms where
    preserves f hf := by
      rw [CategoryTheory.epi_iff_surjective, ConcreteCategory.forget_map_eq_coe,
        ← epi_iff_surjective]
      exact hf

instance forget_preservesMonomorphisms : (forget (ModuleCat.{v} R)).PreservesMonomorphisms where
    preserves f hf := by
      rw [CategoryTheory.mono_iff_injective, ConcreteCategory.forget_map_eq_coe,
        ← mono_iff_injective]
      exact hf

end ModuleCat

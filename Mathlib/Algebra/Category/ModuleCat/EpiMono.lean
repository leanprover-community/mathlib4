/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

#align_import algebra.category.Module.epi_mono from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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

theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v => (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1
set_option linter.uppercaseLean3 false in
#align Module.ker_eq_bot_of_mono ModuleCat.ker_eq_bot_of_mono

theorem range_eq_top_of_epi [Epi f] : LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v => (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1
set_option linter.uppercaseLean3 false in
#align Module.range_eq_top_of_epi ModuleCat.range_eq_top_of_epi

theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f = ⊥ :=
  ⟨fun hf => ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert LinearMap.ker_eq_bot.1 hf⟩
set_option linter.uppercaseLean3 false in
#align Module.mono_iff_ker_eq_bot ModuleCat.mono_iff_ker_eq_bot

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]
set_option linter.uppercaseLean3 false in
#align Module.mono_iff_injective ModuleCat.mono_iff_injective

theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| LinearMap.range_eq_top.1 hf⟩
set_option linter.uppercaseLean3 false in
#align Module.epi_iff_range_eq_top ModuleCat.epi_iff_range_eq_top

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]
set_option linter.uppercaseLean3 false in
#align Module.epi_iff_surjective ModuleCat.epi_iff_surjective

/-- If the zero morphism is an epi then the codomain is trivial. -/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)
set_option linter.uppercaseLean3 false in
#align Module.unique_of_epi_zero ModuleCat.uniqueOfEpiZero

instance mono_as_hom'_subtype (U : Submodule R X) : Mono (ModuleCat.asHomRight U.subtype) :=
  (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)
set_option linter.uppercaseLean3 false in
#align Module.mono_as_hom'_subtype ModuleCat.mono_as_hom'_subtype

instance epi_as_hom''_mkQ (U : Submodule R X) : Epi (↿U.mkQ) :=
  (epi_iff_range_eq_top _).mpr <| Submodule.range_mkQ _
set_option linter.uppercaseLean3 false in
#align Module.epi_as_hom''_mkq ModuleCat.epi_as_hom''_mkQ

instance forget_preservesEpimorphisms : (forget (ModuleCat.{v} R)).PreservesEpimorphisms where
    preserves f hf := by
      erw [CategoryTheory.epi_iff_surjective, ← epi_iff_surjective]
      exact hf
set_option linter.uppercaseLean3 false in
#align Module.forget_preserves_epimorphisms ModuleCat.forget_preservesEpimorphisms

instance forget_preservesMonomorphisms : (forget (ModuleCat.{v} R)).PreservesMonomorphisms where
    preserves f hf := by
      erw [CategoryTheory.mono_iff_injective, ← mono_iff_injective]
      exact hf
set_option linter.uppercaseLean3 false in
#align Module.forget_preserves_monomorphisms ModuleCat.forget_preservesMonomorphisms

end ModuleCat

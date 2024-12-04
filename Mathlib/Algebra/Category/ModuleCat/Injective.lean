/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Module.Injective
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Injective objects in the category of $R$-modules
-/

open CategoryTheory

universe u v
variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
namespace Module

theorem injective_object_of_injective_module [inj : Injective R M] :
    CategoryTheory.Injective (ModuleCat.of R M) where
  factors g f m :=
    have ⟨l, h⟩ := inj.out f ((ModuleCat.mono_iff_injective f).mp m) g
    ⟨l, LinearMap.ext h⟩

theorem injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g := by
    have : CategoryTheory.Mono (ModuleCat.asHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, rfl⟩ := inj.factors (ModuleCat.asHom g) (ModuleCat.asHom f)
    exact ⟨l, fun _ ↦ rfl⟩

theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) :=
  ⟨fun _ => injective_object_of_injective_module R M,
   fun _ => injective_module_of_injective_object R M⟩

end Module


instance ModuleCat.ulift_injective_of_injective.{v'}
    [Small.{v} R] [AddCommGroup M] [Module R M]
    [CategoryTheory.Injective <| ModuleCat.of R M] :
    CategoryTheory.Injective <| ModuleCat.of R (ULift.{v'} M) :=
  Module.injective_object_of_injective_module
    (inj := Module.ulift_injective_of_injective
      (inj := Module.injective_module_of_injective_object _ _))

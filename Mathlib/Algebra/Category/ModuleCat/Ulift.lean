/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
/-!

# Ulift Functor of ModuleCat

-/

universe u v v'

variable (R : Type u) [Ring R]

open CategoryTheory

namespace ModuleCat

/-- Universe lift functor for `R`-module. -/
@[simps obj map]
def uliftFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where
  obj X := ModuleCat.of R (ULift.{v', v} X)
  map f := ModuleCat.ofHom <|
    ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp ULift.moduleEquiv.toLinearMap)
  map_id := by simp
  map_comp f g := by
    ext
    simp

/-- The universe lift functor for `R`-module is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage f := ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap))

instance : (uliftFunctor R).Additive where
  map_add {X Y f g} := by
    simp only [uliftFunctor, hom_add, LinearMap.add_comp, LinearMap.comp_add]
    rfl

lemma uliftFunctor_map_exact (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) :
    (S.map (uliftFunctor R)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  simp only [uliftFunctor, ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ShortComplex.map_f, hom_ofHom, LinearMap.coe_comp, LinearEquiv.coe_coe, ShortComplex.map_g]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨y, hy⟩ ↦ ⟨ULift.moduleEquiv y, hy⟩⟩
  use ULift.moduleEquiv.symm (R := R) y
  simpa

instance : Limits.PreservesFiniteLimits (uliftFunctor.{u, v, v'} R) := by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{u, v, v'} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.1

instance : Limits.PreservesFiniteColimits (uliftFunctor.{u, v, v'} R) := by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{u, v, v'} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.2

instance [Small.{v} R] : (uliftFunctor.{u, v, v'} R).PreservesProjectiveObjects where
  projective_obj {M} proj := by
    let _ : Small.{max v v', u} R := small_lift R
    let _ := (IsProjective.iff_projective M).mpr proj
    rw [← IsProjective.iff_projective]
    exact Module.Projective.of_equiv ULift.moduleEquiv.symm

instance [Small.{v} R] : (uliftFunctor.{u, v, v'} R).PreservesInjectiveObjects where
  injective_obj {M} inj := (Module.injective_iff_injective_object R _).mp
    (Module.ulift_injective_of_injective R ((Module.injective_iff_injective_object R M).mpr inj))

end ModuleCat

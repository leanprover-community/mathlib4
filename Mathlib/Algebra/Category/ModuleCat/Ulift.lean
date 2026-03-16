/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!

# Ulift functor for ModuleCat

In this file, we define the obvious functor `ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R` and prove
it is exact, fully faithful and preverves projective and injective objects.

-/

@[expose] public section

universe v' v u

variable (R : Type u)

open CategoryTheory

namespace ModuleCat

section Ring

variable [Ring R]

/-- Universe lift functor for `R`-module. -/
@[simps obj map, pp_with_univ]
def uliftFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where
  obj X := ModuleCat.of R (ULift.{v', v} X)
  map f := ModuleCat.ofHom <|
    ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp ULift.moduleEquiv.toLinearMap)

/-- The universe lift functor for `R`-module is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage f := ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap))

/-- The `ULift` functor on `ModuleCat` is compatible with the one defined on categories of types. -/
@[simps!]
def uliftFunctorForgetIso :
    ModuleCat.uliftFunctor.{v'} R ⋙ forget _ ≅
    forget _ ⋙ CategoryTheory.uliftFunctor.{v'} :=
  .refl _

instance : (uliftFunctor.{v', v} R).Full := (fullyFaithfulUliftFunctor R).full

instance : (uliftFunctor.{v', v} R).Faithful := (fullyFaithfulUliftFunctor R).faithful

instance : (uliftFunctor R).Additive where

instance : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R) :=
  let : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R ⋙ forget _) := by
    change Limits.PreservesLimitsOfSize.{v, v} (forget (ModuleCat R) ⋙
      CategoryTheory.uliftFunctor.{v'})
    infer_instance
  Limits.preservesLimits_of_reflects_of_preserves (uliftFunctor.{v', v} R) (forget _)

instance : Limits.PreservesFiniteLimits (uliftFunctor.{v', v} R) :=
  Limits.PreservesLimitsOfSize.preservesFiniteLimits _

lemma uliftFunctor_map_exact (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) :
    (S.map (uliftFunctor R)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_disch

instance : Limits.PreservesFiniteColimits (uliftFunctor.{v', v} R) := by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{v', v} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.2

instance [Small.{v} R] : (uliftFunctor.{v', v} R).PreservesProjectiveObjects where
  projective_obj {M} proj := by
    have := small_lift R
    rw [← IsProjective.iff_projective]
    exact Module.Projective.of_equiv ULift.moduleEquiv.symm

instance [Small.{v} R] : (uliftFunctor.{v', v} R).PreservesInjectiveObjects where
  injective_obj {M} inj := (Module.injective_iff_injective_object R _).mp
    (Module.ulift_injective_of_injective R ((Module.injective_iff_injective_object R M).mpr inj))

end Ring

instance [CommRing R] : (uliftFunctor.{v', v} R).Linear R where

end ModuleCat

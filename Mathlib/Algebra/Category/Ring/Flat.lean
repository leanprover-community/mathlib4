/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.RingHom.Flat

/-! # Flat base change preserves finite limits -/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u v

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Flat)

lemma ModuleCat.preservesFiniteLimits_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, v, max w v} f) := by
  rw [(ModuleCat.extendScalars f).preservesFiniteLimits_tfae.out 3 0 rfl]
  rintro S hS
  refine ⟨(((ModuleCat.extendScalars f).preservesFiniteColimits_tfae.out 3 0 rfl rfl).mp
    inferInstance S hS).1, ?_⟩
  rw [ModuleCat.mono_iff_injective]
  algebraize [f]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ ((mono_iff_injective _).mp hS.mono_f)

-- Note that it always preserves all colimits (available via `infer_instance`)
lemma CommRingCat.preservesFiniteLimits_pushout_of_flat
    (hφ : φ.hom.Flat) : PreservesFiniteLimits (Under.pushout φ) := by
  constructor
  intro J _ _
  suffices PreservesLimitsOfShape J (Under.pushout φ ⋙ (commAlgCatEquivUnder S).inverse) from
    preservesLimitsOfShape_of_reflects_of_preserves (G := (commAlgCatEquivUnder _).inverse) _
  suffices PreservesLimitsOfShape J ((Under.pushout φ ⋙ (commAlgCatEquivUnder S).inverse) ⋙
      forget₂ _ (AlgCat S)) from
    preservesLimitsOfShape_of_reflects_of_preserves  (G := (forget₂ _ (AlgCat S))) _
  suffices PreservesLimitsOfShape J (((Under.pushout φ ⋙ (commAlgCatEquivUnder S).inverse) ⋙
      forget₂ _ (AlgCat S)) ⋙ forget₂ _ (ModuleCat S)) from
    preservesLimitsOfShape_of_reflects_of_preserves
      (G := forget₂ _ (ModuleCat S)) _
  have := ModuleCat.preservesFiniteLimits_extendScalars _ hφ
  exact preservesLimitsOfShape_of_natIso (pushoutIsoExtendScalars φ).symm

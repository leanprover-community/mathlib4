/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.LeftResolutions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Flat objects in ModuleCat

-/

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace ModuleCat

variable {R : Type u} [CommRing R]

lemma objectPropertyFlat_iff_preservesFiniteLimits_tensorLeft (M : ModuleCat.{u} R) :
    ObjectProperty.flat M ↔ PreservesFiniteLimits (tensorLeft M) := by
  refine ⟨fun h ↦ h.tensorLeft.1, fun h ↦ ?_⟩
  have : ObjectProperty.exactFunctor (tensorLeft M) := ⟨h, inferInstance⟩
  exact ⟨this, ObjectProperty.prop_of_iso _ (BraidedCategory.tensorLeftIsoTensorRight M) this⟩

lemma objectPropertyFlat_iff_moduleFlat (M : ModuleCat.{u} R) :
    ObjectProperty.flat M ↔ Module.Flat R M := by
  rw [objectPropertyFlat_iff_preservesFiniteLimits_tensorLeft]
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]
  constructor
  · intro
    intro S hS
    exact hS.map _
  · intro hM
    exact And.left (((Functor.exact_tfae (tensorLeft M)).out 1 3).1 hM)

instance : HasFunctorialFlatResolutions (ModuleCat.{u} R) :=
  .mk (ModuleCat.projectiveResolutions R) (by
    rintro M ⟨⟨P, hP⟩, ⟨e : P ≅ M⟩⟩
    rw [← IsProjective.iff_projective] at hP
    apply ObjectProperty.prop_of_iso _ e
    rw [objectPropertyFlat_iff_moduleFlat]
    infer_instance)

instance (M : ModuleCat.{u} R) : ((curriedTensor _).obj M).IsLeftAdjoint :=
  inferInstanceAs (tensorLeft M).IsLeftAdjoint

instance (M : ModuleCat.{u} R) : (tensorRight M).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight M)

instance (M : ModuleCat.{u} R) : ((curriedTensor _).flip.obj M).IsLeftAdjoint :=
  inferInstanceAs (tensorRight M).IsLeftAdjoint

instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_shrink.{0, 0, u, u, u} _

example : (HomologicalComplex.quasiIso (ModuleCat.{u} R)
  (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := inferInstance

/-noncomputable example [HasDerivedCategory (ModuleCat.{u} R)] :
    MonoidalCategory (DerivedCategory (ModuleCat.{u} R)) := inferInstance-/

end ModuleCat

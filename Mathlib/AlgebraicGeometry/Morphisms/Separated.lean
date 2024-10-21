/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immmersion.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is separated if the diagonal map is a closed immersion. -/
@[mk_iff]
class IsSeparated : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  diagonal_isClosedImmersion : IsClosedImmersion (pullback.diagonal f) := by infer_instance

namespace IsSeparated

attribute [instance] diagonal_isClosedImmersion

theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

/-- Monomorphisms are separated. -/
instance (priority := 900) isSeparated_of_mono [Mono f] : IsSeparated f where

instance : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (priority := 900) [IsSeparated f] : QuasiSeparated f where

instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  exact MorphismProperty.diagonal_isStableUnderComposition IsClosedImmersion.stableUnderBaseChange

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance

instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

lemma stableUnderBaseChange : MorphismProperty.StableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  exact MorphismProperty.StableUnderBaseChange.diagonal IsClosedImmersion.stableUnderBaseChange

instance : IsLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (R S : CommRingCat.{u}) (f : R ⟶ S) : IsSeparated (Spec.map f) := by
  constructor
  letI := f.toAlgebra
  show IsClosedImmersion (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [diagonal_Spec_map, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  exact .spec_of_surjective _ fun x ↦ ⟨.tmul R 1 x,
    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩

instance (priority := 100) [h : IsAffineHom f] : IsSeparated f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h
  rw [MorphismProperty.arrow_mk_iso_iff @IsSeparated (arrowIsoSpecΓOfIsAffine f)]
  infer_instance

end IsSeparated

end AlgebraicGeometry

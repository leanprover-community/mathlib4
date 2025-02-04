/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!

# Proper morphisms

A morphism of schemes is proper if it is separated, universally closed and (locally) of finite type.
Note that we don't require quasi-compact, since this is implied by universally closed.

-/


noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is proper if it is separated, universally closed and locally of finite type. -/
@[mk_iff]
class IsProper extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f : Prop where

lemma isProper_eq : @IsProper =
    (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType := by
  ext X Y f
  rw [isProper_iff, ← and_assoc]
  rfl

namespace IsProper

instance : MorphismProperty.RespectsIso @IsProper := by
  rw [isProper_eq]
  infer_instance

instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsProper := by
  rw [isProper_eq]
  infer_instance

instance : MorphismProperty.IsMultiplicative @IsProper := by
  rw [isProper_eq]
  infer_instance

instance [IsProper f] [IsProper g] : IsProper (f ≫ g) where

instance (priority := 900) [IsFinite f] : IsProper f where

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsProper := by
  rw [isProper_eq]
  infer_instance

instance : IsLocalAtTarget @IsProper := by
  rw [isProper_eq]
  infer_instance

end IsProper

lemma IsFinite.eq_isProper_inf_isAffineHom :
    @IsFinite = (@IsProper ⊓ @IsAffineHom : MorphismProperty _) := by
  have : (@IsAffineHom ⊓ @IsSeparated : MorphismProperty _) = @IsAffineHom :=
    inf_eq_left.mpr fun _ _ _ _ ↦ inferInstance
  rw [inf_comm, isProper_eq, inf_assoc, ← inf_assoc, this, eq_inf,
    IsIntegralHom.eq_universallyClosed_inf_isAffineHom, inf_assoc, inf_left_comm]

variable {f} in
lemma IsFinite.iff_isProper_and_isAffineHom :
    IsFinite f ↔ IsProper f ∧ IsAffineHom f := by
  rw [eq_isProper_inf_isAffineHom]
  rfl

instance (priority := 100) [IsFinite f] : IsProper f :=
  (IsFinite.iff_isProper_and_isAffineHom.mp ‹_›).1

@[stacks 01W6 "(1)"]
lemma UniversallyClosed.of_comp_of_isSeparated [UniversallyClosed (f ≫ g)] [IsSeparated g] :
    UniversallyClosed f := by
  rw [← Limits.pullback.lift_snd (𝟙 _) f (Category.id_comp (f ≫ g))]
  have := MorphismProperty.pullback_snd (P := @UniversallyClosed) (f ≫ g) g inferInstance
  infer_instance

@[stacks 01W6 "(2)"]
lemma IsProper.of_comp_of_isSeparated [IsProper (f ≫ g)] [IsSeparated g] :
    IsProper f := by
  rw [← Limits.pullback.lift_snd (𝟙 _) f (Category.id_comp (f ≫ g))]
  have := MorphismProperty.pullback_snd (P := @IsProper) (f ≫ g) g inferInstance
  infer_instance

end AlgebraicGeometry

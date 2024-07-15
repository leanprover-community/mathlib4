-- `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-
IIRC Christian Merten is working towards these.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma isAffine_of_closedEmbedding [IsAffine Y] (h : ClosedEmbedding f.1.base) : IsAffine X := sorry

lemma IsClosedImmersion.iff_of_isAffine [IsAffine Y] :
    IsClosedImmersion f ↔ IsAffine X ∧ Function.Surjective (f.app ⊤) := sorry

lemma IsClosedImmersion.isStableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsClosedImmersion := sorry

-- use `IsClosedImmersion.iff_of_isAffine` and the description of `Spec R ⊗ S`.
instance [IsAffine X] [IsAffine Y] : IsClosedImmersion (pullback.diagonal f) := sorry

end AlgebraicGeometry

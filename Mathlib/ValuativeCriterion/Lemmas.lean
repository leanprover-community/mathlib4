import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma isIso_iff_of_isAffine [IsAffine Y] :
    IsIso f ↔ IsAffine X ∧ Function.Bijective (f.app ⊤) := sorry

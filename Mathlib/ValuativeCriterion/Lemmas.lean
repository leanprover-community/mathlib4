import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma isIso_iff_of_isAffine [IsAffine Y] :
    IsIso f ↔ IsAffine X ∧ Function.Bijective (f.app ⊤) := sorry

-- scheme map preserves specialization
lemma schemePreservesSpec (X Y : Scheme) (f : X ⟶ Y) (x x' : X.carrier) (h : x' ⤳ x) : (f.val.base x') ⤳ (f.val.base x) :=
  Specializes.map_of_continuousAt h (map_continuousAt f.val.base x)

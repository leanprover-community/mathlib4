-- `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-
IIRC Christian Merten is working towards these.
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- use `IsClosedImmersion.iff_of_isAffine` and the description of `Spec R ⊗ S`.
instance [IsAffine X] [IsAffine Y] : IsClosedImmersion (pullback.diagonal f) := sorry

end AlgebraicGeometry

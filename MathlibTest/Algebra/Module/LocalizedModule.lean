import Mathlib

/-! We test that the instances on `LocalizedModule` and `Localization` are reducibly equal. -/

variable {R : Type*} [CommRing R] {S : Submonoid R}

example : Localization S = LocalizedModule S R := by
  with_reducible rfl

example : OreLocalization.instMonoid = LocalizedModule.instMonoid (A := R) (S := S) := by
  with_reducible_and_instances rfl

example : (LocalizedModule.instCommRing : CommRing R[S⁻¹]) = OreLocalization.instCommRing := by
  with_reducible_and_instances rfl

example : (LocalizedModule.algebra' : Algebra R (LocalizedModule S R)) =
    OreLocalization.instAlgebra := by
  with_reducible_and_instances rfl

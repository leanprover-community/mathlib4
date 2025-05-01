import Mathlib.AlgebraicGeometry.EllipticCurve.Affine

variable {R : Type*} (E : WeierstrassCurve R) (EA : WeierstrassCurve.Affine R)

deriving instance DecidableEq for WeierstrassCurve

deriving instance DecidableEq for WeierstrassCurve.Affine.Point

instance {k : Type*} [Field k] [DecidableEq k] : DecidablePred (IsUnit : k → Prop) :=
  fun _ ↦ decidable_of_iff _ isUnit_iff_ne_zero.symm

instance [Field R] [DecidableEq R] : Decidable E.IsElliptic :=
  decidable_of_iff _ E.isElliptic_iff.symm

instance [Field R] [DecidableEq R] : Decidable E.IsElliptic :=
  decidable_of_iff _ E.isElliptic_iff.symm

instance [CommRing R] [DecidableEq R] : DecidableRel EA.Equation :=
  fun _ _ ↦ decidable_of_iff _ (EA.equation_iff _ _).symm

instance [CommRing R] [DecidableEq R] : DecidableRel EA.Nonsingular :=
  fun _ _ ↦ decidable_of_iff _ (EA.nonsingular_iff _ _).symm

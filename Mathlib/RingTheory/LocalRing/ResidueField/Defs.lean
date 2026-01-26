import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!

# Residue Field of local rings

## Main definitions

* `IsLocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.
* `IsLocalRing.residue`: The quotient map from a local ring to its residue field.
-/

@[expose] public section

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def ResidueField :=
  R ⧸ maximalIdeal R
deriving CommRing, Inhabited

noncomputable instance ResidueField.field : Field (ResidueField R) :=
  Ideal.Quotient.field (maximalIdeal R)

/-- The quotient map from a local ring to its residue field. -/
def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _

end IsLocalRing

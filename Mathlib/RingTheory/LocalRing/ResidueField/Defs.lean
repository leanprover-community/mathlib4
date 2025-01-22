/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!

# Residue Field of local rings

## Main definitions

* `LocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.
* `LocalRing.residue`: The quotient map from a local ring to its residue field.
-/

namespace LocalRing

variable (R : Type*) [CommRing R] [LocalRing R]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def ResidueField :=
  R ⧸ maximalIdeal R

-- Porting note: failed at `deriving` instances automatically
instance ResidueFieldCommRing : CommRing (ResidueField R) :=
  show CommRing (R ⧸ maximalIdeal R) from inferInstance

instance ResidueFieldInhabited : Inhabited (ResidueField R) :=
  show Inhabited (R ⧸ maximalIdeal R) from inferInstance

noncomputable instance ResidueField.field : Field (ResidueField R) :=
  Ideal.Quotient.field (maximalIdeal R)

/-- The quotient map from a local ring to its residue field. -/
def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _

end LocalRing

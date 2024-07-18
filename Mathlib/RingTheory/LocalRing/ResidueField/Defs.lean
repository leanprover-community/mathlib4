/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Ideal.Quotient

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Residue Field of local rings

## Main definitions

* `LocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.

-/

namespace LocalRing

variable (R : Type*) [CommRing R] [LocalRing R]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def ResidueField :=
  R ⧸ maximalIdeal R
#align local_ring.residue_field LocalRing.ResidueField

end LocalRing

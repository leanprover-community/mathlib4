/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Local rings

## Main definitions

* `LocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.

-/

universe u v w u'

variable {R : Type u} {S : Type v} {T : Type w} {K : Type u'}

namespace LocalRing

section

variable (R) [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing T] [LocalRing T]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
def ResidueField :=
  R ⧸ maximalIdeal R
#align local_ring.residue_field LocalRing.ResidueField

end

end LocalRing

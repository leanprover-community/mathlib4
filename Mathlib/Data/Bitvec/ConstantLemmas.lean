/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

namespace Bitvec

open Bitvec (zero one not)


/-!
  ### Bitwise Negation
  Show how bitwise negation relates the various constants
-/
section Not
  @[simp]
  theorem not_negOne : not (negOne n) = zero n := by
    simp[Bitvec.not, negOne, zero]

  @[simp]
  theorem not_zero : not (zero n) = (negOne n) := by
    simp[Bitvec.not, negOne, zero]

  @[simp]
  theorem not_intMax : not (intMax n) = intMin n := by
    cases n
    . rfl
    . simp[Bitvec.not, intMax, intMin, negOne, zero, Vector.map_cons]

  @[simp]
  theorem not_intMin : not (intMin n) = intMax n := by
    cases n
    . rfl
    . simp[Bitvec.not, intMax, intMin, negOne, zero, Vector.map_cons]
end Not


end Bitvec

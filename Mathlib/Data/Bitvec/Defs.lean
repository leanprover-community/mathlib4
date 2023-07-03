/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Mathlib.Data.Nat.Pow

/-!
# Basic operations on bitvectors

This file established a theory of bitvectors in terms of `Fin`. This representation is
computationally more efficient than the naive representation of bitvectors as a `Vector` of `Bool`s,
and should generally be preferred.

The `Vector`-based can be found as `Bitvec.BitVector`, and might be usefull as an internal detail
of `Bitvec` proofs

-/

/-- `Bitvec` represents fixed-width, signless integers in terms of `Fin`. -/
def Bitvec (n : ℕ) :=
  Fin (2^n)
#align bitvec Bitvec


namespace Bitvec

section Arithmetic

instance : Add (Bitvec n) := inferInstanceAs (Add <| Fin _)
instance : Sub (Bitvec n) := inferInstanceAs (Sub <| Fin _)
instance : Mul (Bitvec n) := inferInstanceAs (Mul <| Fin _)

end Arithmetic

end Bitvec

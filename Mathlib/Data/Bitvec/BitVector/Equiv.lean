/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.BitVector.Defs
import Mathlib.Data.Bitvec.BitVector.Lemmas

/-!
  Establish the equivalence between `Bitvec n` and `Bitvec.BitVector n`, and proof
  how various operations are transported along this equivalence
-/

namespace Bitvec
open Bitvec (BitVector)

@[simp]
abbrev toVector (v : Bitvec n) : Bitvec.BitVector n :=
  BitVector.ofNat n (Fin.val v)

@[simp]
abbrev ofVector (v : Bitvec.BitVector n) : Bitvec n :=
  ⟨v.toNat, v.toNat_lt⟩

variable (x y : BitVector n)

-- theorem add_ofVector : (ofVector x) + (ofVector y) = ofVector (x + y) := by
--   sorry

-- theorem sub_ofVector : (ofVector x) - (ofVector y) = ofVector (x - y) := by
--   sorry

-- theorem mul_ofVector : (ofVector x) * (ofVector y) = ofVector (x * y) := by
--   sorry

end Bitvec

/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.BitVector.Defs

namespace Bitvec
open Bitvec (BitVector)

variable (x y : BitVector n)

-- theorem add_ofVector : (ofVector x) + (ofVector y) = ofVector (x + y) := by
--   sorry

-- theorem sub_ofVector : (ofVector x) - (ofVector y) = ofVector (x - y) := by
--   sorry

-- theorem mul_ofVector : (ofVector x) * (ofVector y) = ofVector (x * y) := by
--   sorry

end Bitvec

/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename

/-!
# Boolean operations

In Lean 3 this file also contained the definitions of `cond`, `bor`, `band` and `bnot`,
the boolean functions. These are in Lean 4 core (as `cond`, `or`, `and` and `not`), but
apparently `xor` didn't make the cut.

-/

#align bor or
#align band and
#align bnot not

/-- Boolean XOR -/
@[inline]
def xor : Bool → Bool → Bool
  | true, false => true
  | false, true => true
  | _, _ => false
#align bxor xor

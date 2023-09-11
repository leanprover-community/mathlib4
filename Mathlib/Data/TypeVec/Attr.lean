/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Lean

/-!
  Adds a `TypeVec` simp attribute.
  Has to be in a separate file from `TypeVec.lean`, since simp attributes cannot be used directly in
  the file that declares them.
-/


/-- simp set for the manipulation of typevec and arrow expressions -/
register_simp_attr typevec

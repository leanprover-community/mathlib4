/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Mathlib.GroupTheory.Perm.Hex.Generated
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public section

namespace PermGroupTest

@[expose] def cycle : Equiv.Perm (Fin 3) := c[0, 1, 2]
@[expose] noncomputable def subgroup : Subgroup (Equiv.Perm (Fin 3)) :=
  Subgroup.closure ({cycle, Equiv.swap (0 : Fin 3) 1} : Set _)

end PermGroupTest

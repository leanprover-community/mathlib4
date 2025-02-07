/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Order.Fin.Basic

/-!
# Limits and colimits indexed by `Fin`

In this file, we show that `0 : Fin (n + 1)` is an initial object
and `Fin.last n` is a terminal object. This allows to compute
limits and colimits indexed by `Fin (n + 1)`, see
`limitOfDiagramInitial` and `colimitOfDiagramTerminal`
in the file `Limits.Shapes.IsTerminal`.

-/

universe v v' u u' w

open CategoryTheory Limits

namespace Fin

variable {n : ℕ}

instance [NeZero n] (i : Fin n) : Unique (0 ⟶ i) where
  default := homOfLE bot_le
  uniq _ := rfl

instance (i : Fin (n + 1)) : Unique (i ⟶ Fin.last n) where
  default := homOfLE le_top
  uniq _ := rfl

variable (n)

/-- `0` is an initial object in `Fin n` when `n ≠ 0`. -/
def zeroIsInitial [NeZero n] : IsInitial (0 : Fin n) := IsInitial.ofUnique _

/-- `Fin.last n` is a terminal object in `Fin (n + 1)`. -/
def lastIsTerminal : IsTerminal (Fin.last n) := IsTerminal.ofUnique _

end Fin

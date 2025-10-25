/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Preorder
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

open CategoryTheory Limits Preorder

namespace Fin

variable (n : ℕ)

/-- `0` is an initial object in `Fin n` when `n ≠ 0`. -/
def isInitialZero [NeZero n] : IsInitial (0 : Fin n) := isInitialBot

/-- `Fin.last n` is a terminal object in `Fin (n + 1)`. -/
def isTerminalLast : IsTerminal (Fin.last n) := isTerminalTop

end Fin

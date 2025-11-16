/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Init
import Mathlib.Lean.Elab.Term

/-!
# Support for `Sort*` and `Type*`.

These elaborate as `Sort u` and `Type u` with a fresh implicit universe variable `u`.
-/

open Lean Elab Term

/-- The syntax `variable (X Y ... Z : Sort*)` creates a new distinct implicit universe variable
for each variable in the sequence. -/
elab "Sort*" : term => return .sort <|← mkFreshLevelParam

/-- The syntax `variable (X Y ... Z : Type*)` creates a new distinct implicit universe variable
`> 0` for each variable in the sequence. -/
elab "Type*" : term => return .sort <| .succ <|← mkFreshLevelParam

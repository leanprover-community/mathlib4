/-
Copyright (c) 2022 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Lean

open Lean

namespace Lean

namespace MVarId

/-- `asserts g l` asserts all the tuples in `l`,
where `l` is a list of tuples of the form `(name, type, val)`.
It returns the resulting goal.

The first element in the list `l` will be asserted first,
and the last element in the list `l` will be asserted last.
In particular, the last element will correspond to the outmost lambda
in the goal that is returned. -/
def asserts (g : MVarId) : List (Name × Expr × Expr) → MetaM MVarId
| [] => pure g
| ((n, ty, val) :: l) => do
  let g₁ ← g.assert n ty val
  asserts g₁ l

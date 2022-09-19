/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/

import Lean

open Lean Meta

/--
matches to expressions of the form `r x y` with `r` a relation and returns
the triple `(r, x, y)` if there is a match. Note that `r` may be obtained
applying a function to arguments.
-/
def relationAppM? (expr : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
  do
    if expr.isApp && (← inferType expr).isProp then
      let baseRel := expr.getAppFn
      let allArgs := expr.getAppArgs
      if allArgs.size < 2 then pure none
      else
        let lhs := allArgs[allArgs.size -2]!
        let rhs := allArgs[allArgs.size -1]!
        if ← isDefEq (← inferType lhs) (← inferType rhs) then
          let mut rel := baseRel
          for i in [0:allArgs.size - 2] do
            rel := mkApp rel allArgs[i]!
          return some (rel, lhs, rhs)
        else return none
    else pure none

/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Lean.Elab.Tactic.Basic

open Lean
open Lean.Meta
open Lean.Elab.Tactic

/-
TODO: Support for metavariables

The `show_term` tactic is meant to cope with metavariables,
and be able to print results like `refine X _ Y`.

In mathlib we achieve this with the following hack:
```
meta def replace_mvars (e : expr) : expr :=
e.replace (λ e' _, if e'.is_mvar then some (unchecked_cast pexpr.mk_placeholder) else none)
```
which replaces all metavariables with underscores.

How would one achieve this in Lean4? Perhaps we're meant to
* delaborate to a `Syntax`,
* replace the metavariables with `(_ : $stx)` (perhaps using `Syntax.replaceM`?),
* and then feed the result into the remainder of the pretty printing pipeline.

The alternatives I can think of are:
* wish for a `pp.mvarsAsBlanks` option for the pretty printer
* string munging after pretty printing
-/

/--
Construct a `Try this: refine ...` or `Try this: exact ...` string which would construct `g`.
-/
def refineString (g : Expr) : TacticM String := do
  let g₁ ← Expr.headBeta <$> (instantiateMVars g)
  -- FIXME we need to replace metavariables with underscores here (see note above).
  let r ← ppExpr g₁
  if g₁.hasExprMVar then s!"Try this: refine {r}" else s!"Try this: exact {r}"

namespace Lean.Elab.Tactic

/--
`showTerm tac` runs `tac`, then prints the generated term in the form
"Try this: exact X Y Z" or "Try this: refine X _ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)
-/
elab tk:"showTerm" t:tactic : tactic => withMainContext do
  let g ← getMainGoal
  evalTactic t
  logInfoAt tk (← refineString (mkMVar g))

end Lean.Elab.Tactic

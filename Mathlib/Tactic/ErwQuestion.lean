/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Elab.Tactic.Basic

/-!
# The `erw?` tactic

`erw? [r]` calls `erw [r]` (note that only a single step is allowed),
and then attempts to identify any subexpression which would block the use of `rw` instead.
It does so by identifying subexpressions which are defeq, but not at reducible transparency.
-/

open Lean Parser.Tactic Elab Tactic Meta

namespace Mathlib.Tactic.Erw?

/--
If set to `true`, `erw?` will log more information as it attempts to identify subexpressions
which would block the use of `rw` instead.
-/
register_option tactic.erw?.verbose : Bool := {
  defValue := false
  descr := "`erw?` logs more information as it attempts to identify subexpressions \
    which would block the use of `rw` instead."
}

/--
`erw? [r]` calls `erw [r]` (note that only a single step is allowed),
and then attempts to identify any subexpression which would block the use of `rw` instead.
It does so by identifying subexpressions which are defeq, but not at reducible transparency.
-/
syntax (name := erw?) "erw? " "[" rwRule "]" : tactic

/--
Check if two expressions are different at reducible transparency.
Attempt to log an info message for the first subexpressions which are different
(but agree at default transparency).
-/
def logDiffs (tk : Syntax) (e₁ e₂ : Expr) : MetaM Bool := do
  withOptions (fun opts => opts.setBool `pp.analyze true) do
  let verbose := (← getOptions).get `tactic.erw?.verbose (defVal := false)
  if ← withReducible (isDefEq e₁ e₂) then
    if verbose then logInfoAt tk m!"{e₁}\n  and\n{e₂}\n  are defeq at reducible transparency."
    -- They agree at reducible transparency, we're done.
    return false
  else
    if verbose then logInfoAt tk m!"{e₁}\n  and\n{e₂}\n  are not defeq at reducible transparency."
    if ← isDefEq e₁ e₂ then
      match e₁, e₂ with
      | Expr.app f₁ a₁, Expr.app f₂ a₂ =>
        if ← logDiffs tk a₁ a₂ then
          return true
        else if ← logDiffs tk f₁ f₂ then
          return true
        else
          logInfoAt tk m!"{e₁}\n  and\n{e₂}\n  \
            are defeq at default transparency, but not at reducible transparency."
          return true
      | Expr.const _ _, Expr.const _ _ =>
        logInfoAt tk m!"{e₁}\n  and\n{e₂}\n  \
            are defeq at default transparency, but not at reducible transparency."
        return true
      | _, _ =>
        if verbose then logInfoAt tk m!"{e₁}\n  and\n{e₂}\n  are not both applications."
        return false
    else
      if verbose then logInfoAt tk m!"{e₁}\n  and\n{e₂}\n  are not defeq at default transparency."
      return false

elab_rules : tactic
  | `(tactic| erw?%$tk [$r]) => withMainContext do
    let verbose := (← getOptions).get `tactic.erw?.verbose (defVal := false)
    let g ← getMainGoal
    evalTactic (← `(tactic| erw [$r]))
    let e := (← instantiateMVars (mkMVar g)).headBeta
    match e.getAppFnArgs with
    | (``Eq.mpr, #[_, _, e, _]) =>
      match e.getAppFnArgs with
      | (``id, #[ty, e]) =>
        match ty.eq? with
        | some (_, tgt, _) =>
          if verbose then logInfoAt tk m!"Expression appearing in target: {tgt}"
          match (← inferType e).eq? with
          | some (_, inferred, _) =>
            if verbose then logInfoAt tk m!"Expression from `erw`: {inferred}"
            _ ← logDiffs tk tgt inferred
          | _ => logErrorAt tk "Unexpected term produced by `erw`, \
                   inferred type is not an equality."
        | _ => logErrorAt tk "Unexpected term produced by `erw`, type hint is not an equality."
      | _ => logErrorAt tk "Unexpected term produced by `erw`, not of the form: `Eq.mpr (id _) _`."
    | _ => logErrorAt tk "Unexpected term produced by `erw`, head is not an `Eq.mpr`."

end Mathlib.Tactic.Erw?

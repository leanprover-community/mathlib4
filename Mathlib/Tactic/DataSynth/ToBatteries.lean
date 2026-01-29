/-
Copyright (c) 2025 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
import Mathlib.Tactic.FunProp.ToBatteries

namespace Mathlib.Meta.DataSynth

open Lean Meta Mathlib.Meta.FunProp

/-- Perform non-trivial decomposition of `fn = q(fun _ => _)` into
`f` and `g` such that `fn = f∘g`. -/
def lambdaDecompose (fn : Expr) : MetaM (Option (Expr × Expr)) := do
  let .lam xname xtype b bi := fn
    | return none

  withLocalDecl xname bi xtype fun xvar => do
    let b := b.instantiate1 xvar

    b.withApp fun headFn args => do

      if headFn.hasLooseBVars then return none

      let taggedArgs := Array.range args.size |>.zip args
      let depTaggedArgs := taggedArgs.filter (fun (_, arg) => arg.containsFVar xvar.fvarId!)

      if depTaggedArgs.size = 0 then return none

      let gbody ← mkProdElem (depTaggedArgs.map (·.2))
      let g ← mkLambdaFVars #[xvar] gbody
      let .some (_, Y) := (← inferType g).arrow? | return none

      let f ←
        withLocalDeclD `y Y fun y => do
          let ys ← mkProdSplitElem y depTaggedArgs.size

          let mut args' := args
          for (i, _) in depTaggedArgs, yi in ys do
            args' := args'.set! i yi

          mkLambdaFVars #[y] (headFn.beta args')

      -- not non-trivial decomposition
      if ← isDefEq f fn then return none

      return (f, g)

end Mathlib.Meta.DataSynth

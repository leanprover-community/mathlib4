/-
Copyright (c) 2022 Evan Lohn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Lohn, Mario Carneiro
-/

import Mathlib.Util.Tactic

namespace Mathlib.Tactic.ClearValue
open Lean Meta Elab Tactic Term

syntax (name := clearValue) "clear_value" (ppSpace colGt ident)* : tactic

/--
`clear_value [e₀, e₁, e₂, ...]` clears the body of the local definitions `e₀`, `e₁`, `e₂`, ...
changing them into regular hypotheses. A hypothesis `e : α := t` is changed to `e : α`. The order of
locals `e₀`, `e₁`, `e₂` does not matter as a permutation will be chosen so as to preserve type
correctness. This tactic is called `clearbody` in Coq.
-/
elab (name := clear_value) "clear_value" hs:(ppSpace colGt ident)* : tactic  => do
  liftMetaTactic1 fun goal => do
    let ctx ← getLCtx
    let hs ← hs.mapM fun h => return (h, ← getNameAndLocalDecl ctx h)
    let hs := hs.qsort fun a b => a.2.2.index > b.2.2.index
    let mut goal := goal
    for (syn, name, dec) in hs do
      let (deps, goal') ← Meta.revert goal (#[dec.fvarId])
      let .letE v t d b _ ← getMVarType goal'
        | throwErrorAt syn "Cannot clear the body of {name}. It is not a local definition."
      let e := mkForall v .default t b
      _ ← inferType e <|>
        throwErrorAt syn "Cannot clear the body of {name}. The resulting goal is not type correct."
      let g ← withMVarContext goal' (mkFreshExprMVar e)

      assignExprMVar goal' (g.app d)
      let (_, g) ← introNP g.mvarId! deps.size
      goal := g
    pure goal

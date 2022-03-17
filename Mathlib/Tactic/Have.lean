/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/
import Lean

def Lean.Parser.Term.haveIdLhs' :=
  optional (ident >> many (ppSpace >>
    checkColGt "expected to be indented" >>
    (simpleBinderWithoutType <|> bracketedBinder))) >> optType

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta Parser.Term

syntax "have " haveIdLhs' : tactic

elab_rules : tactic
| `(tactic|have $[$n:ident]? $[: $t:term]?) =>
  withMainContext do
    let name : Name := match n with
      | none   => `this
      | some n => n.getId
    let t ← match t with
      | none   => mkFreshTypeMVar
      | some t => elabTerm t none
    liftMetaTactic fun mvarId => do
      let p ← mkFreshExprMVar (userName := name) t
      let mvarIdNew ← assert mvarId name t p
      let (_, mvarIdNew) ← intro1P mvarIdNew
      return [p.mvarId!, mvarIdNew]

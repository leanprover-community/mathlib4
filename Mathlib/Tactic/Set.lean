/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ian Benway.
-/
import Lean
namespace Mathlib.Tactic
open Lean Elab Elab.Tactic Meta

syntax setArgsRest := ppSpace ident (" : " term)? " := " term (" with " "←"? ident)?

syntax (name := set) "set" "!"? setArgsRest : tactic

macro "set!" rest:setArgsRest : tactic => `(tactic|set ! $rest:setArgsRest)

/--
`set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.

`set a := t with ← h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by
  set y := x with ← h2
  sorry
/-
x : Nat
y : Nat := x
h : y + y - y = 3
h2 : x = y
⊢ y + y - y = 3
-/
```

-/
elab_rules : tactic
| `(tactic| set $[!%$rw]? $a:ident $[: $ty:term]? := $val:term $[with $[←%$rev]? $h:ident]?) => do
  withMainContext do
    let (ty, val) ← match ty with
    | some ty =>
      let ty ← Term.elabType ty
      pure (ty, ← elabTermEnsuringType val ty)
    | none =>
      let val ← elabTerm val none
      pure (← inferType val, val)
    let fvar ← liftMetaTacticAux fun mvarId => do
      let (fvar, mvarId) ← intro1P (← define mvarId a.getId ty val)
      pure (fvar, [mvarId])
    withMainContext do
      Term.addTermInfo (isBinder := true) a (mkFVar fvar)
  if rw.isNone then
    evalTactic (← `(tactic| try rewrite [(id rfl : $val = $a)] at *))
  match h, rev with
  | some h, some none =>
    evalTactic (← `(tactic| have $h : $a = $val := rfl))
  | some h, some (some _) =>
    evalTactic (← `(tactic| have $h : $val = $a := rfl))
  | _, _ => pure ()

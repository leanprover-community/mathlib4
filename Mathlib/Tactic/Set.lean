/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ian Benway.
-/
import Lean
namespace Mathlib.Tactic
open Lean Elab.Tactic Meta

private def defineV (nm : Name) (tp : Expr) (tme : Expr) : TacticM Unit := do
  liftMetaTactic1 fun mvarId => do
    let h2 ← (define mvarId nm tp tme)
    let (h, h2) ← intro1P h2
    withMVarContext h2 do
      return h2

/--
`set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.

`set a := t with ←h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by
  set y := x with ←h2
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

syntax (name := set) "set" "!"? ident (" : " term)? " := " term (" with " "←"? ident)? : tactic
elab_rules : tactic
|`(tactic| set $[!%$rw?]? $a:ident $[: $tp?:term]? := $pv:term $[with $[←%$rev?]? $h?:ident]?) => do
  withMainContext do
  match tp? with
  | some t =>
    let te ← elabTerm t (none)
    let pv ← elabTerm pv te
    defineV a.getId te pv
  | none     =>
    let pv ← elabTerm pv (none)
    let te ← inferType pv
    defineV a.getId te pv
  match rw? with
  | some r => evalTactic (← `(tactic| try rw [(id rfl : $pv = $a)] at *))
  | none => evalTactic (← `(tactic| skip))

  match (h?, rev?) with
  | (some h, some (none))    =>
    let hl ← evalTactic (← `(tactic| have $h : $a = $pv := rfl))
  | (some h, some (some r))  =>
    let hl ← evalTactic (← `(tactic| have $h : $pv = $a := rfl))
  | _    =>  evalTactic (← `(tactic| skip))

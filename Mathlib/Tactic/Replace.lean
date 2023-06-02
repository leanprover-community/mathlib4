/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
import Lean
import Mathlib.Tactic.Have

namespace Mathlib.Tactic

open Lean Elab.Tactic

/--
Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

```lean
f : α → β
h : α
⊢ goal
```

Then after `replace h := f h` the state will be:

```lean
f : α → β
h : β
⊢ goal
```

whereas `have h := f h` would result in:

```lean
f : α → β
h† : α
h : β
⊢ goal
```

This can be used to simulate the `specialize` and `apply at` tactics of Coq.
-/
syntax "replace" haveDecl : tactic

elab_rules : tactic
  | `(tactic| replace $[$n?:ident]? $[: $t?:term]? := $v:term) =>
    withMainContext do
      let name : Name := match n? with
      | none   => `this
      | some n => n.getId
      let hId? := (← getLCtx).findFromUserName? name |>.map fun d ↦ d.fvarId
      evalTactic $ ← `(tactic| have $[$n?]? $[: $t?]? := $v)
      match hId? with
      | some hId =>
        try replaceMainGoal [← (← getMainGoal).clear hId]
        catch | _ => pure ()
      | none     => pure ()

/--
Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

Then after `replace h : β` the state will be:

```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h : β
⊢ goal
```

whereas `have h : β` would result in:

```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h✝ : α
h : β
⊢ goal
```
-/
syntax (name := replace') "replace" Parser.Term.haveIdLhs' : tactic

elab_rules : tactic
| `(tactic| replace $[$n:ident $bs*]? $[: $t:term]?) => withMainContext do
    let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t false
    let name : Name := match n with
    | none   => `this
    | some n => n.getId
    let hId? := (← getLCtx).findFromUserName? name |>.map fun d ↦ d.fvarId
    match hId? with
    | some hId =>
      try replaceMainGoal [goal1, ← goal2.clear hId]
      catch | _ => pure ()
    | none     => replaceMainGoal [goal1, goal2]

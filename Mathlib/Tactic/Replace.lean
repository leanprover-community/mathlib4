/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
import Lean

namespace Mathlib.Tactic

open Lean Elab.Tactic

syntax "replace " haveDecl : tactic

/--
Acts like `have`, but removes a hypothesis with the same name as
this one. For example, if the state is:

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

Where `have h := f h` would result in:

```lean
f : α → β
h† : α
h : β
⊢ goal
```

This can be used to simulate the `specialize` and `apply at` tactics of Coq.
-/
elab_rules : tactic
  | `(tactic|replace $[$n?:ident]? $[: $t?:term]? := $v:term) =>
    withMainContext do
      let name : Name := match n? with
      | none   => `this
      | some n => n.getId
      let hId? := (← getLCtx).findFromUserName? name |>.map fun d => d.fvarId
      evalTactic $ ← `(tactic|have $[$n?]? $[: $t?]? := $v)
      match hId? with
      | some hId => replaceMainGoal [← Meta.clear (← getMainGoal) hId]
      | none     => pure ()

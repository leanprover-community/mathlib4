/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module topology.tactic
! leanprover-community/mathlib commit 79abf670d5f946912964c232736e97a761f29ebb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.AutoCases
import Mathbin.Tactic.Tidy
import Mathbin.Tactic.WithLocalReducibility
import Mathbin.Tactic.ShowTerm
import Mathbin.Topology.Basic

/-!
# Tactics for topology

Currently we have one domain-specific tactic for topology: `continuity`.

-/


/-!
### `continuity` tactic

Automatically solve goals of the form `continuous f`.

Mark lemmas with `@[continuity]` to add them to the set of lemmas
used by `continuity`.
-/


/-- User attribute used to mark tactics used by `continuity`. -/
@[user_attribute]
unsafe def continuity : user_attribute
    where
  Name := `continuity
  descr := "lemmas usable to prove continuity"
#align continuity continuity

-- Mark some continuity lemmas already defined in `topology.basic`
attribute [continuity] continuous_id continuous_const

#print continuous_id' /-
-- As we will be using `apply_rules` with `md := semireducible`,
-- we need another version of `continuous_id`.
@[continuity]
theorem continuous_id' {α : Type _} [TopologicalSpace α] : Continuous fun a : α => a :=
  continuous_id
#align continuous_id' continuous_id'
-/

namespace Tactic

/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic to apply `continuous.comp` when appropriate.

Applying `continuous.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `continuous f`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `continuous (λ x, f x)` and
  produce new goals `continuous (λ x, x)`, `continuous f`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
unsafe def apply_continuous.comp : tactic Unit :=
  sorry
#align tactic.apply_continuous.comp tactic.apply_continuous.comp

/-- List of tactics used by `continuity` internally. -/
unsafe def continuity_tactics (md : Transparency := reducible) : List (tactic String) :=
  [intros1 >>= fun ns => pure ("intros " ++ " ".intercalate (ns.map fun e => e.toString)),
    apply_rules [] [`` continuity] 50 { md } >> pure "apply_rules with continuity",
    apply_continuous.comp >> pure "refine continuous.comp _ _"]
#align tactic.continuity_tactics tactic.continuity_tactics

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- Solve goals of the form `continuous f`. `continuity?` reports back the proof term it found.
-/
unsafe def continuity (bang : parse <| optional (tk "!")) (trace : parse <| optional (tk "?"))
    (cfg : tidy.cfg := { }) : tactic Unit :=
  let md := if bang.isSome then semireducible else reducible
  let continuity_core := tactic.tidy { cfg with tactics := continuity_tactics md }
  let trace_fn := if trace.isSome then show_term else id
  trace_fn continuity_core
#align tactic.interactive.continuity tactic.interactive.continuity

/-- Version of `continuity` for use with auto_param. -/
unsafe def continuity' : tactic Unit :=
  continuity none none { }
#align tactic.interactive.continuity' tactic.interactive.continuity'

/-- `continuity` solves goals of the form `continuous f` by applying lemmas tagged with the
`continuity` user attribute.

```
example {X Y : Type*} [topological_space X] [topological_space Y]
  (f₁ f₂ : X → Y) (hf₁ : continuous f₁) (hf₂ : continuous f₂)
  (g : Y → ℝ) (hg : continuous g) : continuous (λ x, (max (g (f₁ x)) (g (f₂ x))) + 1) :=
by continuity
```
will discharge the goal, generating a proof term like
`((continuous.comp hg hf₁).max (continuous.comp hg hf₂)).add continuous_const`

You can also use `continuity!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`continuity?` reports back the proof term it found.
-/
add_tactic_doc
  { Name := "continuity / continuity'"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.continuity, `tactic.interactive.continuity']
    tags := ["lemma application"] }

end Interactive

end Tactic


/-
Copyright (c) 2022 Evan Lohn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Lohn, Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# The `substs` macro

The `substs` macro is a deprecated version of the `subst` tactic that allowed for more than one
hypothesis. Since `subst` now also supports multiple hypotheses, `substs` is deprecated.
-/

public meta section

namespace Mathlib.Tactic.Substs

/-- Deprecated: this functionality exists in `subst` now. -/
syntax (name := substs) "substs" (colGt ppSpace ident)* : tactic

open Lean Meta Elab.Tactic Meta.Tactic.TryThis in
elab_rules : tactic
| `(tactic| substs%$tk $xs:ident*) => withMainContext do
  let stx ← getRef
  let tac ← `(tactic| subst $[$xs]*)
  Lean.logWarningAt tk m!"Deprecation warning: `substs` can be replaced with `subst`."
  Lean.Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := stx)
  evalTactic tac

end Substs

end Mathlib.Tactic

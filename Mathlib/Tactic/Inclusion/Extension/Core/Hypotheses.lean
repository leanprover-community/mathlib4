/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Extension.Core.Family
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Generic hypothesis extensions for the `inclusion` tactic

This file registers hypothesis rules that work for every represented-set implementation.
-/

public meta section

open Lean Meta

namespace Inclusion

attribute [hypothesisOp core] ToSet.mem_of_eq_of_mem ToSet.mem_of_mem_of_eq

/-- The generic hypothesis extension that uses a closed `ToSet` membership hypothesis directly as
an inclusion hypothesis. -/
@[hypothesisExt core | _ ∈ _]
meta def directMembershipHyp : HypothesisExt where
  derive h := do
    let type ← instantiateMVars (← inferType h)
    let some (expr, set, _) := toSetMem? type | failure
    if set.hasFVar || set.hasMVar then
      trace[Tactic.inclusion] "Ignoring non-closed direct hypothesis {type}"
      failure
    let some iExpr ← requestedIVar? expr | return
    addInclusionHyp iExpr ⟨set, h⟩

end Inclusion

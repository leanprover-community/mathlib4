/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Core.ToSet
public meta import Mathlib.Tactic.Inclusion.Extension.Core.Init
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Core extensions for the `inclusion` tactic

This file defines inclusion and hypothesis extensions for the core inclusion family.
-/

public meta section

open Lean Meta

namespace Inclusion

attribute [inclusionOp core] IntervalBool.not_mem IntervalBool.and_mem IntervalBool.or_mem
attribute [hypothesisOp core] ToSet.mem_of_eq_of_mem ToSet.mem_of_mem_of_eq

/-- `HypothesisExt` for direct `ToSet` instance membership hypotheses. -/
@[hypothesisExt core | _ ∈ _]
def instMembershipHyp : HypothesisExt where
  derive h := do
    let type ← instantiateMVars (← inferType h)
    let some (expr, set, _) := toSetMem? type | failure
    if set.hasFVar || set.hasMVar then failure
    let some iVar ← findIVar? expr | failure
    addInclusionHyp iVar.iExpr ⟨set, h⟩

/-- `HypothesisExt` for conjunction hypotheses. -/
@[hypothesisExt core | _ ∧ _]
def andHyp : HypothesisExt where
  derive h := do
    let (``And, #[_, _]) := (← instantiateMVars (← inferType h)).getAppFnArgs | failure
    runHypothesisExts (← mkAppM ``And.left #[h])
    runHypothesisExts (← mkAppM ``And.right #[h])

end Inclusion

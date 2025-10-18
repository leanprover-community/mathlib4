/-
Copyright (c) 2025 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
import Mathlib.Init
import Lean.Server.InfoUtils
import Lean.Meta.TryThis

/-!
# Additions to `Lean.Elab.InfoTree.Main`
-/

namespace Lean.Elab

open Lean.Meta
open Lean.Meta.Tactic.TryThis

/--
Collects all suggestions from all `TryThisInfo`s in `trees`.
`trees` is visited in order and suggestions in each tree are collected in post-order.
-/
def collectTryThisSuggestions (trees : PersistentArray InfoTree) :
    Array Suggestion :=
  go.run #[] |>.2
where
  /-- Visits all trees. -/
  go : StateM (Array Suggestion) Unit := do
    for tree in trees do
      tree.visitM' (postNode := visitNode)
  /-- Visits a node in a tree. -/
  @[nolint unusedArguments]
  visitNode (_ctx : ContextInfo) (i : Info) (_children : PersistentArray InfoTree) :
      StateM (Array Suggestion) Unit := do
    let .ofCustomInfo ci := i
      | return
    let some tti := ci.value.get? TryThisInfo
      | return
    modify (·.push tti.suggestion)

end Lean.Elab

/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Linter.UnusedInstancesInType
public import Mathlib.Tactic.Linter.OverlappingInstances

/-!
# Declaration type linters

We bundle a number of linters that act on declaration types into a single linter:

- The overlapping instances linter
- The unused `Fintype` in type linter
- The unused `Decidable` in type linter

We bundle them because each of them acts on the `Lean.Elab.Term.BodyInfo` in the info tree,
and it is expensive to do this search many times over.

These linters run even if the declaration contains an error.
This is important because it means that a user will get a warning as soon as possible.
-/

public meta section

namespace Mathlib.Linter

open Lean Elab Linter OverlappingInstances UnusedInstancesInType

/-- Run all of the instance parameter linters.
This linter collects the declaration bodies from the info trees,
so that this work does not need to be duplicated. -/
def declTypeLinter : Linter where
  run := withSetOptionIn fun cmd => do
    let opts ← getLinterOptions
    let overlap := getLinterValue linter.overlappingInstances opts
    let decidable := getLinterValue linter.unusedDecidableInType opts
    let fintype := getLinterValue linter.unusedFintypeInType opts
    unless overlap || decidable || fintype do return
    profileitM Exception "declTypeLinter" (← getOptions) do
    for t in ← getInfoTrees do
      for (bodyRef, ctx, info) in t.getDeclBodyInfos do
        if overlap then
          overlappingInstances bodyRef ctx info
        if let some declName := ctx.parentDecl? then
          if let some thm := (← getEnv).findTheoremConstVal? declName then
            Command.liftCoreM do
            if decidable then unusedDecidableInType thm bodyRef
            if fintype then unusedFintypeInType thm bodyRef

initialize addLinter declTypeLinter

end Mathlib.Linter

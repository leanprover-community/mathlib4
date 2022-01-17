/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

/-!
Defines term syntax to call unsafe functions.

```
def cool :=
  unsafe (unsafeCast () : Nat)

#eval cool
```
-/

namespace Mathlib.TermUnsafe
open Lean Meta Elab Term

def mkAuxName (hint : Name) : TermElabM Name :=
  withFreshMacroScope do
    let name := (← getDeclName?).getD Name.anonymous ++ hint
    addMacroScope (← getMainModule) name (← getCurrMacroScope)

elab "unsafe " t:term : term <= expectedType => do
  let t ← elabTerm t expectedType
  let t ← instantiateMVars t
  let t ← if !t.hasExprMVar then t else
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars t
  if ← logUnassignedUsingErrorInfos (← getMVars t) then throwAbortTerm
  let t ← mkAuxDefinitionFor (← mkAuxName `unsafe) t
  let Expr.const unsafeFn unsafeLvls .. ← t.getAppFn | unreachable!
  let ConstantInfo.defnInfo unsafeDefn ← getConstInfo unsafeFn | unreachable!
  let implName ← mkAuxName `impl
  addDecl <| Declaration.defnDecl {
    name := implName
    type := unsafeDefn.type
    levelParams := unsafeDefn.levelParams
    value := (← mkOfNonempty unsafeDefn.type)
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.safe
  }
  setImplementedBy implName unsafeFn
  mkAppN (mkConst implName unsafeLvls) t.getAppArgs

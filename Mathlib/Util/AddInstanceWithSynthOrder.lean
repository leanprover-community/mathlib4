/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Lean.Elab.Command
import Lean.Meta.Instances

/-!
# Add instance with specified synthesization order
-/

namespace Lean.Meta

private def mkInstanceKey (e : Expr) : MetaM (Array InstanceKey) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    DiscrTree.mkPath type tcDtConfig

def addInstanceWithSynthOrder (declName : Name) (attrKind : AttributeKind) (prio : Nat)
    (synthOrder : Array Nat) : MetaM Unit := do
  let c ← mkConstWithLevelParams declName
  let keys ← mkInstanceKey c
  addGlobalInstance declName attrKind
  instanceExtension.add { keys, val := c, priority := prio, globalName? := declName, attrKind, synthOrder } attrKind

end Lean.Meta

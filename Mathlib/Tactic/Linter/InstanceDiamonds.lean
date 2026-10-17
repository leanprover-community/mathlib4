/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Batteries.Tactic.Lint.Basic

/-!
# Linter for instance diamonds

This environment linter checks each global data-carrying instance,
and tries to synthesize another instance that provides the same data.
If these instances are not definitionally equal at instances transparency,
then it gives a warning.
-/

meta section

namespace Mathlib.Linter.InstanceDiamonds

open Lean Meta

/-- Given an instance `inst` of class `cls`, return its data-carrying projections that are
reached through instance projections. Only return the leaf projections.
Assume that `inst` is a data-carrying instance.

For example for `inst : CommMonoid M`, we return the projections
`inst.toMul : Mul M`, `inst.toOne : One M` and `inst.toNPow : NPow M`.
-/
partial def getInstanceDataProjections (cls : Name) (inst : Expr) (acc : Array Expr := #[]) :
    StateRefT NameSet MetaM (Array Expr) := do
  let some info := getStructureInfo? (← getEnv) cls | return acc
  let type ← whnf (← inferType inst)
  let .const _ us := type.getForallBody.getAppFn |
    throwError "internal instance diamonds error: `{inst}` is not an instance"
  let mut acc := acc
  let mut anyParent := false
  for info in info.parentInfo do
    let parent := info.structName
    if (← get).contains parent then continue
    modify (·.insert parent)
    if (← getConstInfo parent).type.getForallBody.isProp then continue
    unless ← isInstance info.projFn do continue
    let proj := .app (mkAppN (.const info.projFn us) type.getAppArgs) inst
    acc ← getInstanceDataProjections parent proj acc
    anyParent := true
  if !anyParent then
    acc := acc.push inst
  return acc

/-- Try to synthesize an instance with the same type as `e`, and if it is not definitionally
equal to `e`, return a warning message. -/
def compareWithSynthesized (e : Expr) : MetaM (Option MessageData) := do
  let type ← inferType e
  let .some inst ← trySynthInstance type | return none
  if ← withImplicit <| isDefEq e inst then
    return none
  if ← withDefault <| isDefEq e inst then
    return m!"The instance{indentExpr e} : {← inferType e}\n\
      is not definitionally equal (at implicit transparency) to{indentExpr inst}"
  else
    -- TODO: Also warn about proper diamonds
    return none

/-- If `declName` is an instance, and is not a theorem, then temporarily remove it from the
global instances, and compare each of its projections with the instance that is found by
type class search. -/
def findDiamonds (declName : Name) : MetaM (Option MessageData) := do
  unless ← isInstance declName do return none
  let cinfo ← getConstInfo declName
  if cinfo.isTheorem then return none
  withoutModifyingEnv do withExporting do withReducible do
  let s ← (instanceExtension.getState (← getEnv)).erase declName
  modifyEnv (instanceExtension.modifyState · fun _ => s)
  forallTelescopeReducing cinfo.type fun xs cls ↦ do
    let some cls ← isClass? cls | return none
    let inst := mkAppN (.const declName (cinfo.levelParams.map .param)) xs
    let mut firstMsg : Option MessageData := none
    let mut later : Array Expr := #[]
    for proj in ← (getInstanceDataProjections cls inst).run' {} do
      if let some msg ← compareWithSynthesized proj then
        if firstMsg.isNone then
          firstMsg := some msg
        else
          later := later.push proj
    firstMsg.mapM fun msg ↦ do
      let mut msg := msg
      if !later.isEmpty then
        msg := m!"{msg}\nSimilarly for {later}"
      addMessageContext msg

/-- The instance diamonds linter tries to find bad instance diamonds that don't unify at
implicit transparency. -/
@[env_linter]
public def instanceDiamonds : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No bad instance diamonds"
  errorsFound := "FOUND BAD INSTANCE DIAMONDS"
  test := fun declName => do
    if declName.isInternal then return none
    findDiamonds declName

end Mathlib.Linter.InstanceDiamonds

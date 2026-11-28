/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Batteries.Tactic.Lint.Basic
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Linter for instance diamonds

This environment linter checks each global data-carrying instance,
and tries to synthesize another instance for each of its data projections.
If these instances are not definitionally equal at `implicit` transparency,
then it gives a warning.

The linter only does this for the full projections and not for partial projections
(so this includes `Mul α` but excludes `Semigroup α` for a `Ring α` instance).
This makes the linter significantly faster,
but in some edge cases this can cause it to miss a diamond.
-/

meta section

namespace Mathlib.Linter.InstanceDiamonds

open Lean Meta

/--
Given an instance `inst` of a data-carrying type class `cls`,
return its data-carrying projections that are reached through instance projections.
Only return the leaf projections.

For example for `inst : CommMonoid M`, we return the projections
`inst.toMul : Mul M`, `inst.toOne : One M` and `inst.toNPow : NPow M`.
-/
partial def getInstanceDataProjections (cls : Name) (inst : Expr) (env : Environment)
    (acc : Array Expr) : StateRefT NameSet MetaM (Array Expr) := do
  let some info := getStructureInfo? env cls | return acc
  (← whnf (← inferType inst)).withApp fun clsConst clsArgs ↦ do
  let .const _ us := clsConst |
    throwError "internal instance diamonds error: `{inst}` is not an instance"
  let mut acc := acc
  let mut anyParent := false
  for { structName, projFn, .. } in info.parentInfo do
    if !wasOriginallyTheorem env projFn && isInstanceCore env projFn then
      anyParent := true
      unless (← get).contains structName do
        modify (·.insert structName)
        let proj := .app (mkAppN (.const projFn us) clsArgs) inst
        acc ← getInstanceDataProjections structName proj env acc
  if !anyParent then
    acc := acc.push inst
  return acc

/--
Try to synthesize an instance with the same type as `e`, and if it is not definitionally
equal to `e`, return a warning message.
-/
def compareWithSynthesized (e : Expr) : MetaM (Option MessageData) := do
  let type ← inferType e
  let .some inst ← trySynthInstance type | return none
  if ← withImplicit <| isDefEq e inst then
    return none
  if ← withDefault <| isDefEq e inst then
    return m!"This equality does not hold at implicit transparency:\n\
      `({e} : {← inferType e}) = {inst}`"
  else
    -- TODO: Also warn about proper diamonds:
    -- return m!"This equality does not hold definitionally, causing an instance diamond:\n\
    --   `({e} : {← inferType e}) = {inst}`"
    return none

/--
If `declName` is an instance, and is not a theorem, then temporarily remove it from the
global instances, and compare each of its projections with the instance that is found by
type class search.
-/
def findDiamonds (declName : Name) : MetaM (Option MessageData) := do
  let env ← getEnv
  unless isInstanceCore env declName do return none
  if wasOriginallyTheorem env declName then return none
  let cinfo ← getConstVal declName
  withoutModifyingEnv do withExporting do withReducible do
  let s ← (instanceExtension.getState (← getEnv)).erase declName
  modifyEnv (instanceExtension.modifyState · fun _ => s)
  forallTelescopeReducing cinfo.type fun xs cls ↦ do
    let some cls ← isClass? cls | return none
    let inst := mkAppN (.const declName (cinfo.levelParams.map .param)) xs
    let mut firstMsg : Option MessageData := none
    let mut later : Array Expr := #[]
    for proj in ← (getInstanceDataProjections cls inst env #[]).run' {} do
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
  test declName := do
    if declName.isInternal then return none
    findDiamonds declName

end Mathlib.Linter.InstanceDiamonds

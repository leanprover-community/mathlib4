/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.Simp.SimpCongrTheorems
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# The `congrFixedArgs` linter

The `congrFixedArgs` linter emits a warning when a theorem is given the `@[congr]` attribute, but
some explicit argument of the function in its conclusion is the same on both sides. This is in
direct violation of the recommendation in the documentation of `@[congr]`.

When `simp` uses a bad congruence theorem like this, it never visits that argument.
Usually `simp` will revisit the resulting expression and simplify the argument later, but this
doesn't happen with `singlePass := true`, or when a `post` method returns `.done`
(as in `norm_cast`), so the argument is left unsimplified.

Arguments which are proofs or types, and arguments on which later arguments depend, are ignored.
-/

meta section

open Lean Meta Elab Command Linter

namespace Mathlib.Linter

/-- The `congrFixedArgs` linter emits a warning when a theorem is given the `@[congr]` attribute,
but some explicit argument of the function in its conclusion is the same on both sides, in violation
of the recommendation in the documentation of `@[congr]`. -/
public register_option linter.congrFixedArgs : Bool := {
  defValue := true
  descr := "enable the congrFixedArgs linter"
}

namespace CongrFixedArgs

/-- Given a theorem `declName` whose conclusion is `f a₁ ... aₙ = f b₁ ... bₙ` (or `↔`) for a
constant `f`, returns the name of `f` together with the positions `i` of the explicit arguments of
`f` for which `aᵢ` and `bᵢ` are the same. Arguments which are proofs or types, and those on which
later arguments of `f` depend, are skipped. -/
def fixedArgs (declName : Name) : MetaM (Option (Name × Array Nat)) := do
  let (_, _, type) ← forallMetaTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
  let some (lhs, rhs) := type.eqOrIff? | return none
  let some fnName := lhs.getAppFn.constName? | return none
  let fnInfo ← getFunInfoNArgs lhs.getAppFn lhs.getAppNumArgs
  let lhsArgs := lhs.getAppArgs
  let rhsArgs := rhs.getAppArgs
  let mut fixed := #[]
  for h : i in [:lhsArgs.size] do
    let some pinfo := fnInfo.paramInfo[i]? | continue
    if pinfo.binderInfo.isExplicit && !pinfo.hasFwdDeps && some lhsArgs[i] == rhsArgs[i]? then
      unless (← isProof lhsArgs[i]) || (← isType lhsArgs[i]) do
        fixed := fixed.push i
  return some (fnName, fixed)

/-- Logs a warning at `ref` if `declName` is a `@[congr]` theorem with fixed explicit arguments. -/
def lintCongrTheorem (ref : Syntax) (declName : Name) : CommandElabM Unit := do
  let some (fnName, fixed) ← liftTermElabM <| fixedArgs declName | return
  -- `@[congr]` theorems are indexed by the head function of their conclusion.
  unless (congrExtension.getState (← getEnv)).get fnName |>.any (·.theoremName == declName) do
    return
  if fixed.isEmpty then return
  let binderNames := (← getConstInfo fnName).type.getForallBinderNames.toArray
  let args := fixed.toList.map fun i ↦ m!"`{binderNames[i]?.getD `_}` (argument #{i + 1})"
  logLint linter.congrFixedArgs ref m!"\
    The `@[congr]` theorem `{.ofConstName declName}` does not allow the following explicit \
    arguments of `{.ofConstName fnName}` to change: {MessageData.joinSep args ", "}. \
    This violates the recommendation in the documentation of `@[congr]`."

@[inherit_doc Mathlib.Linter.linter.congrFixedArgs]
def congrFixedArgsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.congrFixedArgs (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- Only commands which mention the `congr` attribute can add `@[congr]` theorems.
  let some congrAttr := stx.find? fun s ↦
    s.isOfKind ``Lean.Parser.Attr.simple && s[0].getId == ``congr | return
  let env ← getEnv
  let mut linted : NameSet := {}
  -- `attribute [congr] foo bar`: lint the named theorems.
  for s in stx.topDown do
    unless s.isOfKind ``Lean.Parser.Command.attribute do continue
    for id in s[4].getArgs do
      let some declName ← (do return some (← liftCoreM <| realizeGlobalConstNoOverload id))
        <|> pure none | continue
      unless linted.contains declName do
        linted := linted.insert declName
        lintCongrTheorem id declName
  -- `@[congr] theorem foo ...`: lint the `@[congr]` theorems declared in this command.
  let some cmdRange := stx.getRange? | return
  for (_, thms) in (congrExtension.getState env).lemmas.toList do
    for thm in thms do
      let declName := thm.theoremName
      if linted.contains declName || (env.getModuleIdxFor? declName).isSome then continue
      let some ranges ← findDeclarationRanges? declName | continue
      let pos := (← getFileMap).ofPosition ranges.range.pos
      if cmdRange.start ≤ pos && pos < cmdRange.stop then
        linted := linted.insert declName
        lintCongrTheorem congrAttr declName

initialize addLinter congrFixedArgsLinter

end CongrFixedArgs

end Mathlib.Linter

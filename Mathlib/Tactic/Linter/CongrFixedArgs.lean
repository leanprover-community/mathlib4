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

/-- Given a `@[congr]` theorem `thm` whose conclusion is `f a₁ ... aₙ = f b₁ ... bₙ` (or `↔`),
returns the positions `i` of the explicit arguments of `f` for which `aᵢ` and `bᵢ` are the same.
Arguments which are proofs or types, and those on which later arguments of `f` depend, are
skipped. -/
def fixedArgs (thm : SimpCongrTheorem) : MetaM (Array Nat) := do
  let (_, _, type) ← forallMetaTelescopeReducing (← getConstInfo thm.theoremName).type
  let some (lhs, rhs) := type.eqOrIff? | return #[]
  let fnInfo ← getFunInfoNArgs lhs.getAppFn lhs.getAppNumArgs
  let args := lhs.getAppArgs.zip <| rhs.getAppArgs.zip fnInfo.paramInfo
  let fixed : Array Bool ← args.mapM fun (a, b, p) ↦ do
    return p.binderInfo.isExplicit && !p.hasFwdDeps && a == b && !(← isProof a) && !(← isType a)
  return fixed.zipIdx.filterMap (fun x ↦ if x.fst == true then some x.snd else none)

/-- Logs a warning at `ref` if the `@[congr]` theorem `thm` has fixed explicit arguments. -/
def lintCongrTheorem (ref : Syntax) (thm : SimpCongrTheorem) : CommandElabM Unit := do
  let fixed ← liftTermElabM <| fixedArgs thm
  if fixed.isEmpty then return
  -- Display each argument as `x : T`, as in the signature of the head function.
  let args ← liftTermElabM <| forallTelescopeReducing (← getConstInfo thm.funName).type fun xs _ ↦
    fixed.filterMapM fun i ↦ do
      let some x := xs[i]? | return none
      addMessageContext m!"`{x} : {← inferType x}`"
  logLint linter.congrFixedArgs ref m!"\
    The `@[congr]` theorem `{.ofConstName thm.theoremName}` does not allow the following explicit \
    arguments of `{.ofConstName thm.funName}` to change:\
      {indentD (MessageData.joinSep args.toList "\n")}\n\
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
  let congrThms := (congrExtension.getState env).lemmas.toList.flatMap (·.2)
  let mut linted : NameSet := {}
  -- `attribute [congr] foo bar`: lint the named theorems.
  for s in stx.topDown do
    unless s.isOfKind ``Lean.Parser.Command.attribute do continue
    for id in s[4].getArgs do
      let some declName ← (do return some (← liftCoreM <| realizeGlobalConstNoOverload id))
        <|> pure none | continue
      let some thm := congrThms.find? (·.theoremName == declName) | continue
      unless linted.contains declName do
        linted := linted.insert declName
        lintCongrTheorem id thm
  -- `@[congr] theorem foo ...`: lint the `@[congr]` theorems declared in this command.
  let some cmdRange := stx.getRange? | return
  for thm in congrThms do
    let declName := thm.theoremName
    if linted.contains declName || (env.getModuleIdxFor? declName).isSome then continue
    let some ranges ← findDeclarationRanges? declName | continue
    let pos := (← getFileMap).ofPosition ranges.range.pos
    if cmdRange.start ≤ pos && pos < cmdRange.stop then
      linted := linted.insert declName
      lintCongrTheorem congrAttr thm

initialize addLinter congrFixedArgsLinter

end CongrFixedArgs

end Mathlib.Linter

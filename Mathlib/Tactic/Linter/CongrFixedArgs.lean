/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Meta.CongrTheorems
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

The linter only considers explicit non-type arguments which `simp` would rewrite with the default
congruence procedure. In particular, proofs, instances, and arguments on which later
non-proof arguments depend are ignored, as are types.
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
returns the positions `i` of the explicit non-type arguments of `f` for which `aᵢ` and `bᵢ` are the
same, but which `simp` would rewrite with the default congruence procedure. -/
def fixedArgs (thm : SimpCongrTheorem) : MetaM (Array Nat) := do
  let (_, _, type) ← forallMetaTelescopeReducing (← getConstInfo thm.theoremName).type
  let some (lhs, rhs) := type.eqOrIff? | return #[]
  let fnInfo ← getFunInfoNArgs lhs.getAppFn lhs.getAppNumArgs
  let kinds ← getCongrSimpKinds lhs.getAppFn fnInfo
  let args := lhs.getAppArgs.zip <| rhs.getAppArgs.zip <| fnInfo.paramInfo.zip kinds
  let fixed : Array Bool ← args.mapM fun (a, b, p, k) ↦ do
    return p.binderInfo.isExplicit && (k matches .eq) && a == b && !(← isType a)
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

/-- Whether `stx` is the `congr` attribute. -/
def isCongrAttr (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Attr.simple && stx[0].getId == ``congr

/-- The identifiers `foo bar` in the `attribute [congr] foo bar` commands occurring in `stx`. -/
def congrAttributeTargets (stx : Syntax) : Array Syntax := Id.run do
  let mut ids := #[]
  for s in stx.topDown do
    -- `attribute [attrs,*] ids*`
    if s.isOfKind ``Lean.Parser.Command.attribute && (s[2].find? isCongrAttr).isSome then
      ids := ids ++ s[4].getArgs
  return ids

@[inherit_doc Mathlib.Linter.linter.congrFixedArgs]
def congrFixedArgsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.congrFixedArgs (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- Only commands which mention the `congr` attribute can add `@[congr]` theorems.
  let some congrAttr := stx.find? isCongrAttr | return
  let env ← getEnv
  let congrThms := (congrExtension.getState env).lemmas.toList.flatMap (·.2)
  let mut linted : NameSet := {}
  -- `attribute [congr] foo bar`: lint the named theorems.
  for id in congrAttributeTargets stx do
    let declName ← try liftCoreM <| realizeGlobalConstNoOverload id catch _ => continue
    -- This fails for `attribute [local congr] foo in ...`, whose attribute is already gone.
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

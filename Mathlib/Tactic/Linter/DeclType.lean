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

- The concrete instances linter, which is defined in this file
- The overlapping instances linter
- The unused `Fintype` in type linter
- The unused `Decidable` in type linter

We bundle them because each of them acts on the `Lean.Elab.Term.BodyInfo` in the info tree,
and it is expensive to do this search many times over.

These linters run even if the declaration contains an error.
This is important because it means that a user will get a warning as soon as possible.
-/

meta section

namespace Mathlib.Linter

open Lean Meta Elab Command Linter

section concreteInstances

/--
The `concreteInstances` linter flags any instance assumption whichout variables.
If such a type class has an instance, then this should be declared as a instance globally,
instead of assumed as a local hypothesis. And if there is no instance, then the assumption
can never be satisfied.
-/
register_option linter.concreteInstances : Bool := {
  defValue := true
  descr := "enable the concrete instances linter"
}

/-- Return the instance hypotheses in the given type that have no (universe) variables. -/
def getConcreteInstanceAssumptions : Expr → List Expr
  | .forallE _ d b bi =>
    if bi.isInstImplicit && !d.hasLooseBVars && !d.hasLevelParam then
      d :: getConcreteInstanceAssumptions b
    else
      getConcreteInstanceAssumptions b
  | _ => []

/-- Report a warning message if there are any concrete instances in the local context. -/
def runConcreteLinter (constVal : ConstantVal) (bodyRef : Syntax) : CommandElabM Unit := do
  let classes := getConcreteInstanceAssumptions constVal.type
  if classes.isEmpty then return
  /- Log the warning from the declaration's selection range (usually the declaration name,
  or `instance`) to the body if possible. This underlines the hypotheses and type,
  and makes the warning visible in the infoview when the cursor is within the body. -/
  let ref := (← findDeclarationSyntaxRange? constVal.name).elim bodyRef
    (mkNullNode #[.ofRange ·, bodyRef])
  Command.liftCoreM do MetaM.run' do
  for cls in classes do
    let some clsName ← isClass? cls | continue
    -- A redundant `Decidable` hypothesis can allow a declaration to be compatible with
    -- all potential `Decidable` instance, so we allow this.
    if clsName == ``Decidable then continue
    if (← trySynthInstance cls) matches .some _ then
      logLint linter.concreteInstances ref
        m!"There exists a global instance of type class `{cls}`.\n\
        Please rely on this instance and remove the `{.sbracket cls}` assumption."
    else
      logLint linter.concreteInstances ref
        m!"The instance assumption `{.sbracket cls}` does not contain free variables.\n\
        Instead of assuming it locally, please add a global instance with\n\
        `instance : {cls} := ...`"

end concreteInstances

open OverlappingInstances UnusedInstancesInType

/-- Run all of the instance parameter linters.
This linter collects the declaration bodies from the info trees,
so that this work does not need to be duplicated. -/
public def declTypeLinter : Linter where
  run := withSetOptionIn fun cmd => do
    let opts ← getLinterOptions
    let overlap := getLinterValue linter.overlappingInstances opts
    let concrete := getLinterValue linter.concreteInstances opts
    let decidable := getLinterValue linter.unusedDecidableInType opts
    let fintype := getLinterValue linter.unusedFintypeInType opts
    unless overlap || concrete || decidable || fintype do return
    profileitM Exception "declTypeLinter" (← getOptions) do
    for t in ← getInfoTrees do
      for (bodyRef, ctx, info) in t.getDeclBodyInfos do
        if overlap then
          overlappingInstances bodyRef ctx info
        if let some declName := ctx.parentDecl? then
          -- TODO: these linters don't work in an `example`,
          -- because then `declName` is never added to the environment.
          if let some (constVal, kind) := (← getEnv).findConstValWithKind? declName then
            if concrete then runConcreteLinter constVal bodyRef
            if kind matches .thm then
              Command.liftCoreM do
              if decidable then unusedDecidableInType constVal bodyRef
              if fintype then unusedFintypeInType constVal bodyRef

initialize addLinter declTypeLinter

end Mathlib.Linter

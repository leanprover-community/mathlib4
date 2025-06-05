/-
Copyright (c) 2025 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/

import Mathlib.Lean.Meta.RefinedDiscrTree

/-! Structure and enviroment extension storing `data_synth` declarations.

-/

open Lean Meta

namespace Mathlib.Meta.DataSynth

/-- Each type of `data_synth` goal like `HasFDerivAt`, `HasFDerivWithinAt` etc. is
called `data_synth` declaration and the structure `DataSynthDecl` stores information on which
arguments are considered as input or output. For example for `HasFDerivAt R f f' x` arguments `R`,
`f` and `x` are considered as input arguments and `f'` as output argument.
-/
structure DataSynthDecl where
  /-- Name of the `data_synth` declaration e.g. `HasFDerivAt`. -/
  name : Name
  /-- Number of arguments of the decalaration e.g. `HasFDerivAt` has 13 arguments including implicit
  and instance implicit arguments. -/
  nargs : Nat
  /-- Indices of arguments that are considered as outputs e.g. for `HasFDerivAt` only `f'` is
  considered as output argument and its index is 11.  -/
  outputArgs : Array Nat
  /-- Input function argument - one argument of function type can be marked as special and custom
  unification rules are applied. In case of `HasFDerivAt` it is the argument `f` with index 10 for
  which custom unification is done to apply composition theorem.  -/
  inputFunArg : Option Nat
  deriving Hashable, Inhabited, BEq

/-- Type for the environment extension storing all `data_synth` declarations. -/
abbrev DataSynthDeclsExt := SimpleScopedEnvExtension DataSynthDecl (NameMap DataSynthDecl)

/-- Environment extension storing all `data_synth` declarations. -/
initialize dataSynthDeclsExt : DataSynthDeclsExt ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := {}
    addEntry := fun d e => d.insert e.name e
  }


/-- Get `data_synth` declaration if `e` is a `data_synth` goal. -/
def getDataSynth? (e : Expr) : MetaM (Option DataSynthDecl) := do

  let e ← whnfR e

  let ext := dataSynthDeclsExt.getState (← getEnv)

  let .some (fnName,_) := e.getAppFn'.const?
    | return none

  let .some DataSynthDecl := ext.find? fnName
    | return none

  if e.getAppNumArgs' = DataSynthDecl.nargs then
    return DataSynthDecl
  else
    return none


/-- Add `data_synth` declaration to the environment. -/
def addDataSynthDecl (declName : Name) (outArgs : Array Name) (inFunArg? : Option Name) :
    MetaM Unit := do

  let info ← getConstInfo declName

  let (xs,_,_) ← forallMetaTelescope info.type

  -- get all argument names
  let argNames ←
    forallTelescope info.type fun xs _ =>
      xs.mapM (fun x => x.fvarId!.getUserName)

  -- convert names to indices
  let outputArgs : Array Nat ←
    outArgs.mapM (fun arg => do
      let some i := argNames.findIdx? (arg==·)
        | throwError "argument {arg} not found"
      pure i)

  -- convert input function argument name to index and check if it is function type
  let inArg? : Option Nat ←
    inFunArg?.mapM fun arg => do
      let some i := argNames.findIdx? (arg==·)
        | throwError "argument {arg} not fuound"
      unless (← inferType xs[i]!).isForall do
        throwError "input function argument {arg} is expected to be function type"
      pure i

  let decl : DataSynthDecl := {
    name := declName
    nargs := xs.size
    outputArgs := outputArgs
    inputFunArg := inArg?
  }

  modifyEnv (dataSynthDeclsExt.addEntry · decl)

end Mathlib.Meta.DataSynth

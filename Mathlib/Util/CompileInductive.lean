/-
Copyright (c) 2023 Parth Shastri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parth Shastri, Gabriel Ebner, Mario Carneiro
-/
import Lean.Compiler.CSimpAttr
import Lean.Elab.PreDefinition

/-!
# Define the `compile_inductive%` command.

The command `compile_inductive% Foo` adds compiled code for the recursor `Foo.rec`,
working around a bug in the core Lean compiler which does not support recursors.

For technical reasons, the recursor code generated by `compile_inductive%`
unfortunately evaluates the base cases eagerly.  That is,
`List.rec (unreachable!) (fun _ _ _ => 42) [42]` will panic.

Similarly, `compile_def% Foo.foo` adds compiled code for definitions when missing.
This can be the case for type class projections, or definitions like `List._sizeOf_1`.
-/

namespace Mathlib.Util

open Lean

private def replaceConst (repl : AssocList Name Name) (e : Expr) : Expr :=
  e.replace fun | .const n us => repl.find? n |>.map (.const · us) | _ => none

open Meta

private def mkFunExts' (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut e := e
  for x in xs.reverse do
    e ← mkFunExt (← mkLambdaFVars #[x] e)
  return e

private def mkFunExts (e : Expr) : MetaM Expr := do
  forallTelescope (← inferType e) fun xs _ => mkFunExts' xs (mkAppN e xs)

open Elab

/-- Returns the names of the recursors for a nested or mutual inductive,
using the `all` and `numMotives` arguments from `RecursorVal`. -/
def mkRecNames (all : List Name) (numMotives : Nat) : List Name :=
  if numMotives ≤ all.length then
    all.map mkRecName
  else
    let main := all[0]!
    all.map mkRecName ++
      (List.range (numMotives - all.length)).map (fun i => main.str s!"rec_{i+1}")

/--
Compile the definition `dv` by adding a second definition `dv✝` with the same body,
and registering a `csimp`-lemma `dv = dv✝`.
-/
def compileDefn (dv : DefinitionVal) : TermElabM Unit := do
  if ((← getEnv).getModuleIdxFor? dv.name).isNone then
    -- If it's in the same module then we can safely just call `compileDecl`
    -- on the original definition
    return ← compileDecl <| .defnDecl dv
  let name ← mkFreshUserName dv.name
  addAndCompile <| .defnDecl { dv with name }
  let levels := dv.levelParams.map .param
  let old := .const dv.name levels
  let new := .const name levels
  let name ← mkFreshUserName <| dv.name.str "eq"
  addDecl <| .thmDecl {
    name
    levelParams := dv.levelParams
    type := ← mkEq old new
    value := ← mkEqRefl old
  }
  Compiler.CSimp.add name .global

/--
`compile_def% Foo.foo` adds compiled code for the definition `Foo.foo`.
This can be used for type class projections or definitions like `List._sizeOf_1`,
for which Lean does not generate compiled code by default
(since it is not used 99% of the time).
-/
elab tk:"compile_def% " i:ident : command => Command.liftTermElabM do
  let n ← resolveGlobalConstNoOverloadWithInfo i
  let dv ← withRef i <| getConstInfoDefn n
  withRef tk <| compileDefn dv

private def compileStruct (iv : InductiveVal) (rv : RecursorVal) : TermElabM Unit := do
  let name ← mkFreshUserName rv.name
  addAndCompile <| .defnDecl { rv with
    name
    value := ← forallTelescope rv.type fun xs _ =>
      let val := xs[rv.getFirstMinorIdx]!
      let val := mkAppN val ⟨.map (xs[rv.getMajorIdx]!.proj iv.name) <| .range rv.rules[0]!.nfields⟩
      mkLambdaFVars xs val
    hints := .abbrev
    safety := .safe
  }
  let levels := rv.levelParams.map .param
  let old := .const rv.name levels
  let new := .const name levels
  let name ← mkFreshUserName <| rv.name.str "eq"
  addDecl <| .mutualDefnDecl [{
    name
    levelParams := rv.levelParams
    type := ← mkEq old new
    value := .const name levels
    hints := .opaque
    safety := .partial
  }]
  Compiler.CSimp.add name .global
  compileDefn <| ← getConstInfoDefn <| mkRecOnName iv.name

/--
Generate compiled code for the recursor for `iv`.
-/
def compileInductive (iv : InductiveVal) : TermElabM Unit := do
  let rv ← getConstInfoRec <| mkRecName iv.name
  if ← isProp rv.type then
    logWarning m!"not compiling {rv.name}"
    return
  if (← getEnv).contains (rv.name.str "_cstage2") ||
    (Compiler.CSimp.ext.getState (← getEnv)).map.contains rv.name
  then
    logWarning m!"already compiled {rv.name}"
    return
  if !iv.isRec && rv.numMotives == 1 && iv.numCtors == 1 && iv.numIndices == 0 then
    compileStruct iv rv
    return
  let levels := rv.levelParams.map .param
  let rvs ←
    if rv.numMotives == 1 then pure [rv]
    else mkRecNames iv.all rv.numMotives |>.mapM getConstInfoRec
  let rvs ← rvs.mapM fun rv => return (rv, ← mkFreshUserName rv.name)
  let repl := rvs.foldl (fun l (rv, name) => .cons rv.name name l) .nil
  addAndCompile <| .mutualDefnDecl <|← rvs.mapM fun (rv, name) => do
    pure { rv with
      name
      value := ← forallTelescope rv.type fun xs body => do
        let major := xs[rv.getMajorIdx]!
        (← whnfD <| ← inferType major).withApp fun head args => do
          let .const iv levels' := head | throwError "not an inductive"
          let iv ← getConstInfoInduct iv
          let rv' ← getConstInfoRec <| mkRecName iv.name
          if !iv.isRec && rv'.numMotives == 1 && iv.numCtors == 1 && iv.numIndices == 0 then
            let rule := rv.rules[0]!
            let val := .beta (replaceConst repl rule.rhs) xs[:rv.getFirstIndexIdx]
            let val := .beta val ⟨.map (major.proj iv.name) <| .range rule.nfields⟩
            mkLambdaFVars xs val
          else
            let val := .const (mkCasesOnName iv.name) (.param rv.levelParams.head! :: levels')
            let val := mkAppN val args[:rv'.numParams]
            let val := .app val <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] body
            let val := mkAppN val xs[rv.getFirstIndexIdx:]
            let val := mkAppN val <| rv.rules.toArray.map fun rule =>
              .beta (replaceConst repl rule.rhs) xs[:rv.getFirstIndexIdx]
            mkLambdaFVars xs val
      hints := .opaque
      safety := .partial
    }
  for (rv, name) in rvs do
    let old := .const rv.name levels
    let new := .const name levels
    let name ← mkFreshUserName <| rv.name.str "eq"
    addDecl <| .mutualDefnDecl [{
      name
      levelParams := rv.levelParams
      type := ← mkEq old new
      value := .const name levels
      hints := .opaque
      safety := .partial
    }]
    Compiler.CSimp.add name .global
  for name in iv.all do
    for aux in [mkRecOnName name, mkBRecOnName name] do
      if let some (.defnInfo dv) := (← getEnv).find? aux then
        compileDefn dv

/--
`compile_inductive% Foo` creates compiled code for the recursor `Foo.rec`,
so that `Foo.rec` can be used in a definition
without having to mark the definition as `noncomputable`.
-/
elab tk:"compile_inductive% " i:ident : command => Command.liftTermElabM do
  let n ← resolveGlobalConstNoOverloadWithInfo i
  let iv ← withRef i <| getConstInfoInduct n
  withRef tk <| compileInductive iv

compile_inductive% Nat
compile_inductive% List
compile_inductive% PUnit
compile_inductive% PEmpty
compile_inductive% And
compile_inductive% False
compile_inductive% Empty
compile_def% List._sizeOf_1
compile_def% List._sizeOf_inst

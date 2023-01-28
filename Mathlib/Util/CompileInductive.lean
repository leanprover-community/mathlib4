/-
Copyright (c) 2023 Parth Shastri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parth Shastri
-/
import Lean.Compiler.CSimpAttr
import Lean.Elab.Predefinition

/-!
# Define the `#compile inductive` command.
-/

namespace Mathlib.Util

open Lean

private def replaceConst (old new : Name) (e : Expr) : Expr :=
  e.replace λ | .const n us => if n == old then some (.const new us) else none | _ => none

open Meta

private def mkFunExts' (xs : Array Expr) (e : Expr) (βfg : Expr × Expr × Expr) : MetaM Expr :=
  Prod.fst <$> xs.foldrM (init := (e, βfg)) λ x (e, β, f, g) => do
    let α ← inferType x
    let f ← mkLambdaFVars #[x] f
    let g ← mkLambdaFVars #[x] g
    return (
      mkApp5
        (.const ``funext [(← inferType α).sortLevel!, (← inferType β).sortLevel!])
        α
        (← mkLambdaFVars #[x] β)
        f
        g
        (← mkLambdaFVars #[x] e),
      ← mkForallFVars #[x] β,
      f,
      g
    )

private def mkFunExts (e : Expr) : MetaM Expr := do
  forallTelescope (← inferType e) λ xs body => do
    let some βfg := (← whnf body).eq?
      | throwError "expected equality"
    mkFunExts' xs (mkAppN e xs) βfg

private def mkEq (α a b : Expr) : MetaM Expr := do
  return mkApp3 (.const ``Eq [(← inferType α).sortLevel!]) α a b

private def mkEqRefl (α a : Expr) : MetaM Expr := do
  return mkApp2 (.const ``Eq.refl [(← inferType α).sortLevel!]) α a

open Elab

/--
Compile the definition `dv`.
-/
def compileDefn (dv : DefinitionVal) : TermElabM Unit := do
  let name ← mkFreshUserName dv.name
  addAndCompile <| .defnDecl { dv with name }
  let levels := dv.levelParams.map .param
  let old := .const dv.name levels
  let new := .const name levels
  let name ← mkFreshUserName <| dv.name.str "eq"
  addDecl <| .thmDecl {
    name
    levelParams := dv.levelParams
    type := ← mkEq dv.type old new
    value := ← mkEqRefl dv.type old
  }
  Compiler.CSimp.add name .global

/--
`#compile def i` compiles the definition `i`.
-/
elab tk:"#compile " "def " i:ident : command => Command.liftTermElabM do
  let n ← resolveGlobalConstNoOverload i
  let dv ← withRef i <| getConstInfoDefn n
  withRef tk <| compileDefn dv

private def compilePropStruct (iv : InductiveVal) (rv : RecursorVal) : TermElabM Unit := do
  let name ← mkFreshUserName rv.name
  addAndCompile <| .defnDecl { rv with
    name
    value := ← forallTelescope rv.type λ xs _ =>
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
  addDecl <| .thmDecl {
    name
    levelParams := rv.levelParams
    type := ← mkEq rv.type old new
    value := ← forallTelescope rv.type λ xs body => do
      let pf := .const rv.name (.zero :: levels.tail!)
      let pf := mkAppN pf xs[:rv.numParams]
      let old := mkAppN old xs
      let new := mkAppN new xs
      let pf := .app pf <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] <| ← mkEq body old new
      let minor := xs[rv.getFirstMinorIdx]!
      let pf := .app pf <| ← forallTelescope (← inferType minor) λ ys body' => do
        let pf' ← mkEqRefl body' <| mkAppN minor ys
        mkLambdaFVars ys pf'
      let pf := .app pf xs[rv.getMajorIdx]!
      mkFunExts' xs pf (body, old, new)
  }
  Compiler.CSimp.add name .global
  compileDefn <| ← getConstInfoDefn <| mkRecOnName iv.name

/--
Compile the recursor for `iv`.
-/
def compileInductive (iv : InductiveVal) : TermElabM Unit := do
  let rv ← getConstInfoRec <| mkRecName iv.name
  if ← isProp rv.type then
    logWarning m!"not compiling {rv.name}"
    return
  unless rv.numMotives == 1 do
    throwError "mutual/nested inductives unsupported"
  if iv.type.getForallBody.isProp && !iv.isRec && iv.numCtors == 1 && iv.numIndices == 0 then
    compilePropStruct iv rv
    return
  let levels := rv.levelParams.map .param
  let name ← mkFreshUserName rv.name
  addAndCompile <| .mutualDefnDecl [{ rv with
    name
    value := ← forallTelescope rv.type λ xs body => do
      let val := .const (mkCasesOnName iv.name) levels
      let val := mkAppN val xs[:rv.numParams]
      let val := .app val <| ← mkLambdaFVars xs[rv.getFirstIndexIdx:] body
      let val := mkAppN val xs[rv.getFirstIndexIdx:]
      let val := mkAppN val <| rv.rules.toArray.map λ rule =>
        .beta (replaceConst rv.name name rule.rhs) xs[:rv.getFirstIndexIdx]
      mkLambdaFVars xs val
    hints := .opaque
    safety := .partial
  }]
  let old := .const rv.name levels
  let new := .const name levels
  let name ← mkFreshUserName <| rv.name.str "eq"
  addDecl <| .mutualDefnDecl [{
    name
    levelParams := rv.levelParams
    type := ← mkEq rv.type old new
    value := ← forallTelescope rv.type λ xs body => do
      let pf := .const rv.name (.zero :: levels.tail!)
      let pf := mkAppN pf xs[:rv.numParams]
      let old := mkAppN old xs
      let new := mkAppN new xs
      let motive ← mkLambdaFVars xs[rv.getFirstIndexIdx:] <| ← mkEq body old new
      let pf := .app pf motive
      let pf := mkAppN pf <| ← rv.rules.toArray.zip xs[rv.getFirstMinorIdx:] |>.mapM λ (rule, minor) => do
        forallTelescope ((← inferType minor).replaceFVar xs[rv.numParams]! motive) λ ys _ => do
          let minor := mkAppN minor ys[:rule.nfields]
          let pf' ← mkEqRefl (← inferType minor) minor
          let pf' ← ys[rule.nfields:].foldlM (λ pf' y => do mkCongr pf' (← mkFunExts y)) pf'
          mkLambdaFVars ys pf'
      let pf := mkAppN pf xs[rv.getFirstIndexIdx:]
      mkFunExts' xs pf (body, old, new)
    hints := .opaque
    safety := .partial
  }]
  Compiler.CSimp.add name .global
  for aux in [mkRecOnName iv.name, mkBRecOnName iv.name] do
    if let some (.defnInfo dv) := (← getEnv).find? aux then
      compileDefn dv

/--
`#compile inductive i` compiles the recursor for `i`.
-/
elab tk:"#compile " "inductive " i:ident : command => Command.liftTermElabM do
  let n ← resolveGlobalConstNoOverload i
  let iv ← withRef i <| getConstInfoInduct n
  withRef tk <| compileInductive iv

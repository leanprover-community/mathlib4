import Lean
import Mathlib.Tactic

open Lean Meta

inductive LawvereExpr : Type where
  | proj (output : ℕ) : LawvereExpr
  | op (opName : Name) (output : ℕ) : Array LawvereExpr → LawvereExpr
deriving Repr

structure LawvereOp where
  name : Name
  inputs : Array ℕ
  output : ℕ
deriving Repr

structure LawvereAxiom where
  name : Name
  inputs : Array ℕ
  output : ℕ
  lhs : LawvereExpr
  rhs : LawvereExpr
deriving Repr

def Lean.StructureInfo.getType (info : StructureInfo) : MetaM Expr := do
  let env ← getEnv
  let some c := env.find? info.structName
    | throwError "Failed to find {info.structName} in environment."
  return c.type

def Lean.StructureInfo.telescope {α : Type}
    (info : StructureInfo) (e : Array Expr → Expr → MetaM α) : MetaM α := do
  let tp ← info.getType
  Meta.forallTelescope tp e

def Lean.StructureInfo.elabOperations (info : StructureInfo) :
    MetaM (Array LawvereOp) := do
  let mut out := #[]
  let env ← getEnv
  for c in info.fieldInfo do
    let some projFn := env.find? c.projFn | continue
    let .sort u ← Meta.inferType projFn.type | continue
    if u == 0 then continue
    let new ← Meta.forallTelescope projFn.type fun fvars body => do
      let idxOfStruct : ℕ := ← do
        let mut out := 0
        for fvar in fvars do
          out := out + 1
          let (nm, _) := (← Meta.inferType fvar).getAppFnArgs
          if nm == info.structName then return out
        return out
      let sorts := fvars[:idxOfStruct].toArray.pop
      let inputs := fvars[idxOfStruct:].toArray
      let some body := sorts.getIdx? body | throwError "ERROR1"
      let inputs : Array (MetaM (Option ℕ)) := inputs.map fun e => do
        let tp ← Meta.inferType e
        let idx := sorts.getIdx? tp
        return idx
      let inputs : Array (Option ℕ) ← inputs.mapM id
      let inputs : Option (Array ℕ) := inputs.mapM id
      let some inputs := inputs | throwError "ERROR2"
      return .mk c.projFn inputs body
    out := out.push new
  return out

partial
def Lean.Expr.parseLawvereExpr
    (sorts : Array Expr) (ops : Array LawvereOp) (e : Expr) : MetaM LawvereExpr :=
  match e with
  | .app .. => do
    let (nm, args) := e.getAppFnArgs
    let some op := ops.find? fun op => nm == op.name | throwError "ERROR"
    let rest ← args.mapM fun e => e.parseLawvereExpr sorts ops
    return .op op.name op.output rest
  | e => do
    match sorts.getIdx? e with
    | some idx => return .proj idx
    | none => throwError "ERROR2"

def Lean.StructureInfo.elabAxioms (info : StructureInfo) :
    MetaM (Array LawvereAxiom) := do
  let operations ← info.elabOperations
  let mut out := #[]
  let env ← getEnv
  for c in info.fieldInfo do
    let some projFn := env.find? c.projFn | continue
    let .sort u ← Meta.inferType projFn.type | continue
    if u != 0 then continue
    let new ← Meta.forallTelescope projFn.type fun fvars body => do
      let idxOfStruct : ℕ := ← do
        let mut out := 0
        for fvar in fvars do
          out := out + 1
          let (nm, _) := (← Meta.inferType fvar).getAppFnArgs
          if nm == info.structName then return out
        return out
      let sorts := fvars[:idxOfStruct].toArray.pop
      let inputs := fvars[idxOfStruct:].toArray
      let .app (.app (.app (.const ``Eq ..) S) lhs) rhs := body | throwError "ERROR"
      let some sortIndex := sorts.getIdx? S | throwError "ERROR"
      let inputs : Array (MetaM (Option ℕ)) := inputs.map fun e => do
        let tp ← Meta.inferType e
        let idx := sorts.getIdx? tp
        return idx
      let inputs : Array (Option ℕ) ← inputs.mapM id
      let inputs : Option (Array ℕ) := inputs.mapM id
      let some inputs := inputs | throwError "ERROR2"
      return .mk c.projFn inputs sortIndex
        (← lhs.parseLawvereExpr sorts operations)
        (← rhs.parseLawvereExpr sorts operations)
    out := out.push new
  return out

def foobar (str : Name) : MetaM Unit := do
  let env ← getEnv
  let strInfo ← getStructureInfo? env str
  let ops ← strInfo.elabOperations
  IO.println <| repr ops
  let axs ← strInfo.elabAxioms
  IO.println <| repr axs

class AA (X Y : Type*) where
  one : X
  two : Y → X → Y
  mul1 : X → X → X
  ff : X → Y
  mul4 : X → X → X → Y → X → Y
  one_mul (x : X) : ff (mul1 one x) = ff x
  onke_mul (x : X) : ff (mul1 one x) = ff x

#eval foobar `AA

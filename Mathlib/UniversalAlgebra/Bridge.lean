import Lean
import Mathlib.Tactic

open Lean Meta

inductive LawvereExpr : Type where
  -- inputs is part of the data
  | proj (inputs : Array ℕ) (output : ℕ) : LawvereExpr
  -- inputs can be computed recursively in this case.
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
    (e : Expr)
    (sortFVars : Array Expr)
    (inputFVars : Array Expr)
    (ops : Array LawvereOp) :
    MetaM LawvereExpr :=
  match e with
  | .app .. => do
    let (nm, args) := e.getAppFnArgs
    let args ← args.filterM fun e => do
      let tp ← Meta.inferType e
      return sortFVars.contains tp
    let some ⟨nm, _, output⟩ := ops.find? fun e => e.name == nm | throwError "ERROR"
    let args ← args.mapM fun e => e.parseLawvereExpr sortFVars inputFVars ops
    return .op nm output args
  | e => do
    let inputs ← inputFVars.mapM fun e => do
      let tp ← Meta.inferType e
      let some idx := sortFVars.getIdx? tp | throwError "ERROR"
      return idx
    let some output := inputFVars.getIdx? e | throwError "ERROR"
    return .proj inputs output

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
      let sortFVars := fvars[:idxOfStruct].toArray.pop
      let inputFVars := fvars[idxOfStruct:].toArray
      let .app (.app (.app (.const ``Eq ..) S) lhs) rhs := body | throwError "ERROR"
      let some sortIndex := sortFVars.getIdx? S | throwError "ERROR"
      let lhs ← lhs.parseLawvereExpr sortFVars inputFVars operations
      let rhs ← rhs.parseLawvereExpr sortFVars inputFVars operations
      let inputs ← inputFVars.mapM fun e => do
        let tp ← Meta.inferType e
        let some idx := sortFVars.getIdx? tp | throwError "ERROR"
        return idx
      return .mk c.projFn inputs sortIndex lhs rhs
    out := out.push new
  return out

def foobar (str : Name) : MetaM Unit := do
  let env ← getEnv
  let strInfo ← getStructureInfo? env str
  let ops ← strInfo.elabOperations
  IO.println <| repr ops
  let axs ← strInfo.elabAxioms
  IO.println <| repr axs

class Module' (R M : Type*) where
  addR : R → R → R
  mulR : R → R → R
  oneR : R
  zeroR : R
  smul : R → M → M
  addM : M → M → M
  zeroM : M
  addR_assoc (x y z : R) : addR (addR x y) z = addR x (addR y z)
  mulR_assoc (x y z : R) : mulR (mulR x y) z = mulR x (mulR y z)
  addR_comm (x y : R) : addR x y = addR y x


#eval foobar `Module'

import Lean
import Mathlib.Tactic

open Lean Meta

inductive LawvereExpr : Type where
  | proj (inputs : Array ℕ) (output : ℕ) : LawvereExpr
  | op (opName : Name) (output : ℕ) : Array LawvereExpr → LawvereExpr
deriving Repr

partial
instance : ToExpr LawvereExpr where
  toExpr := aux
  toTypeExpr := .const ``LawvereExpr []
where aux :=
  let typeExpr : Expr := .const ``LawvereExpr []
  fun
  | .proj inputs output => mkApp2 (.const ``LawvereExpr.proj []) (toExpr inputs) (toExpr output)
  | .op opName output rest =>
    mkApp3 (.const ``LawvereExpr.op []) (toExpr opName) (toExpr output) <|
      letI exprs := rest.map aux
      mkApp2 (.const ``List.toArray [0]) typeExpr <| exprs.foldr
        (fun a b => mkApp3 (.const ``List.cons [0]) typeExpr a b)
        (.app (.const ``List.nil [0]) typeExpr)

structure LawvereOp where
  name : Name
  inputs : Array ℕ
  output : ℕ
deriving Repr

instance : ToExpr LawvereOp where
  toExpr C := mkApp3 (.const ``LawvereOp.mk []) (toExpr C.name) (toExpr C.inputs) (toExpr C.output)
  toTypeExpr := .const ``LawvereOp []

structure LawvereAxiom where
  name : Name
  inputs : Array ℕ
  output : ℕ
  lhs : LawvereExpr
  rhs : LawvereExpr
deriving Repr

instance : ToExpr LawvereAxiom where
  toExpr C := mkApp5 (.const ``LawvereAxiom.mk [])
    (toExpr C.name) (toExpr C.inputs) (toExpr C.output) (toExpr C.lhs) (toExpr C.rhs)
  toTypeExpr := .const ``LawvereAxiom []

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

structure LawvereContext where
  className : Name
  numSort : Nat
  sortNames : Array Name
  operations : Array LawvereOp
  axioms : Array LawvereAxiom
deriving Repr

instance : ToExpr LawvereContext where
  toExpr C := mkApp5 (.const ``LawvereContext.mk [])
    (toExpr C.className)
    (toExpr C.numSort)
    (toExpr C.sortNames)
    (toExpr C.operations)
    (toExpr C.axioms)
  toTypeExpr := .const ``LawvereContext []

abbrev LawvereM := ReaderT LawvereContext MetaM

def runLawvereM {α : Type} (className : Name) (e : LawvereM α) :
    MetaM α := do
  let env ← getEnv
  let strInfo ← getStructureInfo? env className
  let numSorts ← strInfo.telescope fun as _ => return as.size
  let sortNames ← strInfo.telescope fun as _ => as.filterMapM fun e => do
    let .fvar id := e | return none
    return ← id.getUserName
  let ops ← strInfo.elabOperations
  let axioms ← strInfo.elabAxioms
  e.run <| .mk className numSorts sortNames ops axioms

class Module' (R M : Type*) where
  ff : R → M → R
  gg : R → R → R
  hh : M → M → M
  hh_assoc (x y z : M) : hh (hh x y) z = hh x (hh y z)
  ff_gg (r s : R) (m : M) : ff (gg r s) m = gg r s

def LawvereM.numSorts : LawvereM ℕ := return (← read).numSort
def LawvereM.sortNames : LawvereM (Array Name) := return (← read).sortNames
def LawvereM.operations : LawvereM (Array LawvereOp) := return (← read).operations
def LawvereM.axioms : LawvereM (Array LawvereAxiom) := return (← read).axioms

elab "lawvere_context%" i:ident : term => do
  let nm := i.getId
  runLawvereM nm do
    let ctx ← read
    IO.println <| repr ctx
    return toExpr ctx

class MM (R : Type*) where
  A : R
  h (a : R) : A = a

#eval (lawvere_context% Module')

#eval runLawvereM `Module' do
  let names ← LawvereM.sortNames
  IO.println names
  let ops ← LawvereM.operations
  IO.println "OPS"
  for ⟨nm, input, output⟩ in ops do
    IO.println "---"
    IO.println nm
    IO.println input
    IO.println output
  let axioms ← LawvereM.axioms
  IO.println "AXIOMS"
  for ⟨nm, h1, h2, h3, h4⟩  in axioms do
    IO.println "---"
    IO.println nm
    IO.println h1
    IO.println h2
    IO.println <| repr h3
    IO.println <| repr h4

import Lean
import Mathlib.Tactic

open Lean Meta

class AA (X Y : Type*) where
  one : X
  two : Y → X → Y
  mul : X → X → X
  one_mul (x : X) : mul one x = x

inductive LawvereWord : List Name → List Name → Type where
  | of (opName : Name) (inputs : List Name) (output : Name) : LawvereWord inputs [output]
  | id (sorts : List Name) : LawvereWord sorts sorts
  | comp (A B C : List Name) : LawvereWord A B → LawvereWord B C → LawvereWord A C
  | fst (A B : List Name) : LawvereWord (A ++ B) A
  | snd (A B : List Name) : LawvereWord (A ++ B) B
  | lift (T A B : List Name) : LawvereWord T A → LawvereWord T B → LawvereWord T (A ++ B)
  | toNil (A : List Name) : LawvereWord A []

def foobar (str : Name) : MetaM Unit := do
  let env ← getEnv
  let some constInfo := env.find? str | throwError s!"{str} not found in the environment."
  let tp := constInfo.type
  let numSorts : Array Name ← Meta.forallTelescope tp fun as _ =>
    as.mapM fun e => do
      let .fvar id := e | throwError "error"
      id.getUserName
  IO.println s!"Found the following sort names {numSorts}"
  let some strInfo := getStructureInfo? env str |
    throwError s!"{str} is not the name of a structure in the environment."
  let mut operations : Array (StructureFieldInfo × ConstantInfo) := #[]
  let mut axioms : Array (StructureFieldInfo × ConstantInfo) := #[]
  for c in strInfo.fieldInfo do
    let some projFnConst := env.find? c.projFn | unreachable!
    let Expr.sort u ← Meta.inferType projFnConst.type | continue
    if u == 0 then
      axioms := axioms.push (c, projFnConst)
    else
      operations := operations.push (c, projFnConst)
  IO.println s!"Found {operations.size} operations"
  for (opInfo, opConstInfo) in operations do
    IO.println "---"
    IO.println <| ← Meta.ppExpr opConstInfo.type
    let opData : Array Name × Name ← Meta.forallTelescope opConstInfo.type fun fvars body => do
      let mut inputs : Array Name := #[]
      let mut collect : Bool := False
      for fvar in fvars do
        let .fvar id := fvar | continue
        let tp ← id.getType
        if tp.getAppFnArgs.fst == str then collect := True ; continue
        unless collect do continue
        let .fvar id := tp | continue
        let nm ← id.getUserName
        inputs := inputs.push nm
      let .fvar bodyId := body | throwError "ERROR"
      return (inputs, ← bodyId.getUserName)
    IO.println opData
  for (axmInfo, axmConstInfo) in axioms do
    IO.println "---"
    IO.println <| ← Meta.ppExpr axmConstInfo.type
    let axData : Array Name ← Meta.forallTelescope axmConstInfo.type fun fvars body => do
      let mut vars : Array Name := #[]
      let mut collect : Bool := False
      for fvar in fvars do
        let .fvar id := fvar | continue
        let tp ← id.getType
        if tp.getAppFnArgs.fst == str then collect := True ; continue
        unless collect do continue
        let .fvar id := tp | continue
        let nm ← id.getUserName
        vars := vars.push nm
        match body with
        | .app (.app (.app (.const ``Eq _) S) _) _ =>
          let .fvar id := S | throwError "EEE"
          let output ← id.getUserName
          IO.println s!"Output: {output}"
        | _ => continue
      return vars
    IO.println axData

#eval foobar `AA

import Mathlib

open Lean
structure State where
  visited : NameMap Bool := {}

abbrev M := ReaderT Environment <| StateM (NameMap Bool)

partial def collect (c : Name) : M Bool := do
  let collectExpr (e : Expr) : M Bool := e.getUsedConstants.anyM collect
  let s ← get
  if let some res := s.find? c then
    return res
  let env ← read
  modify fun s => s.insert c false
  let res ← match env.checked.get.find? c with
  | some (ConstantInfo.axiomInfo v)  => collectExpr v.type
  | some (ConstantInfo.defnInfo v)   => collectExpr v.type <||> collectExpr v.value
  | some (ConstantInfo.thmInfo v)    => collectExpr v.type <||> collectExpr v.value
  | some (ConstantInfo.opaqueInfo v) => collectExpr v.type <||> collectExpr v.value
  | some (ConstantInfo.quotInfo _)   => pure false
  | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
  | some (ConstantInfo.recInfo v)    => collectExpr v.type
  | some (ConstantInfo.inductInfo v) => collectExpr v.type <||> v.ctors.anyM collect
  | none                             => pure false
  modify fun s => s.insert c res
  return res

partial def collectAll : M Nat := do
  modify fun s => s.insert ``Classical.choice true
  let env ← read
  let mut count := 0
  for (constName, _) in env.constants do
    let hasChoice ← collect constName
    if hasChoice then count := count + 1
  return count

run_cmd do
  let env ← getEnv
  let count := collectAll.run env |>.run' {}
  Lean.logInfo m!"Found {count} constants depending on Classical.choice"

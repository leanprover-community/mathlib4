import ImportGraph.RequiredModules
import Lean.CoreM
import RefactorGraph.DAG

open Lean Core Std

def importGraph (env : Environment) : IO (DAG Name) := do
  let stderr ← IO.getStderr
  stderr.putStrLn "Computing import graph..."
  stderr.flush
  let modules := env.header.moduleNames
  let mut out : DAG Name := .empty
  for module in modules do
    out := out.insert module (HashSet.ofArray <| env.importsOf module)
  return out

partial def Name.transitivelyUsedConstants (n : Name) : MonadCacheT Name NameSet CoreM NameSet :=
  checkCache n fun _ ↦ do
    let s ← getConstInfo n
    let mut out := {}
    for t in s.getUsedConstantsAsSet do
      if t == n then continue
      out := out.union <| (← transitivelyUsedConstants t).filter (· != n)
    return out

--#eval (Name.transitivelyUsedConstants `Nat).run

def aux (nm : Name) : CoreM Unit := do
  let env ← getEnv
  let mut csts : NameSet := {}
  for (c, i) in env.constants do
    if i.getUsedConstantsAsSet.contains nm then csts := csts.insert c
  println! csts.size


def main (args : List String) : IO Unit := do
  match args with
  | [name] =>
    initSearchPath (← findSysroot)
    let env ← Lean.importModules #[{ module := `Mathlib }] {}
    Prod.fst <$> CoreM.toIO (aux name.toName) { fileName := "input", fileMap := default }
      { env := env }
  | _ =>
    throw <| .userError "Usage: RefactorGraph <name>"

import RefactorGraph.DAG

open Lean Std

def importGraph (env : Environment) : IO (DAG Name) := do
  let stderr ← IO.getStderr
  stderr.putStrLn "Computing import graph..."
  stderr.flush
  let modules := env.header.moduleNames
  let mut out : DAG Name := .empty
  for module in modules do
    out := out.insert module (HashSet.ofArray <| env.importsOf module)
  return out

def importsUsing (env : Environment) (nm : Name) : IO (HashSet Name) := do
  let stderr ← IO.getStderr
  stderr.putStrLn "Computing required imports..."
  stderr.flush
  let mut out := {}
  let mut counter := 0
  let stderr ← IO.getStderr
  for (n,c) in env.constants do
    counter := counter + 1
    if counter % 1000 == 0 then
      stderr.putStr s!"\rProgress: {counter} "
      stderr.flush
    if c.getUsedConstantsAsSet.contains nm then
      let some mod := env.getModuleFor? n | continue
      out := out.insert mod
  return out

def main (args : List String) : IO Unit := do
  match args with
  | [name] =>
    initSearchPath (← findSysroot)
    let env ← Lean.importModules #[{ module := `Mathlib }] {}
    let importGraph ← importGraph env
    let stderr ← IO.getStderr
    stderr.putStrLn "Computing ancestors..."
    stderr.flush
    let importGraph := importGraph.allAncestors
    let importsUsing ← importsUsing env (String.toName name)
    let mut G : DAG Name := .empty
    for mod in importsUsing do
      stderr.putStr s!"\rProcessing {mod}"
      stderr.flush
      let parents := (importGraph.getD mod {}).filter fun n => importsUsing.contains n
      G := G.insert mod parents
    stderr.putStrLn "\nComputing transitive reduction..."
    stderr.flush
    G := G.transitiveReduction
    for node in G.leaves do
      println! node
  | _ =>
    throw <| .userError "Usage: RefactorGraph <name>"

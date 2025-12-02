import Mathlib.Lean.CoreM

open Lean Std

structure DAG (α : Type) [BEq α] [Hashable α] where
  parent : HashMap α (HashSet α)

namespace DAG
variable {α : Type} [BEq α] [Hashable α] (G : DAG α)

def empty : DAG α where parent := {}

def insert (a : α) (bs : HashSet α) : DAG α where
  parent := G.parent.insert a bs

def insertEdge (a b : α) : DAG α where
  parent := G.parent.insert b (G.parent.getD b {} |>.insert a)

/-- Get all ancestors of a node in the DAG. An ancestor of `a` is any node `b`
    such that there exists a path from `b` to `a`. -/
def ancestors (a : α) : HashSet α := Id.run do
  let mut visited : HashSet α := {}
  let mut worklist : Array α := #[]

  -- Add initial parents to worklist
  if let some parents := G.parent[a]? then
    for p in parents do
      worklist := worklist.push p

  -- Process worklist
  repeat
    match worklist.back? with
    | none => break
    | some b =>
      worklist := worklist.pop
      if !visited.contains b then
        visited := visited.insert b
        if let some parents := G.parent[b]? then
          for p in parents do
            worklist := worklist.push p

  return visited

/-- Compute ancestors for all nodes efficiently using topological sort and dynamic programming.
    Returns a HashMap where each node maps to its set of ancestors. -/
def allAncestors : HashMap α (HashSet α) := Id.run do
  -- Compute in-degrees (number of incoming edges to each node)
  let mut inDegree : HashMap α Nat := {}
  -- First, ensure all nodes (including those that only appear as parents) are in the map
  for (node, parents) in G.parent do
    inDegree := inDegree.insert node parents.size
    for p in parents do
      if !inDegree.contains p then
        inDegree := inDegree.insert p 0

  -- Topological sort using Kahn's algorithm
  let mut queue : Array α := #[]
  for (node, deg) in inDegree do
    if deg == 0 then
      queue := queue.push node

  let mut topoOrder : Array α := #[]
  let mut idx := 0
  while h : idx < queue.size do
    let node := queue[idx]
    topoOrder := topoOrder.push node
    idx := idx + 1

    -- For each child of this node (nodes that have this node as a parent)
    for (child, parents) in G.parent do
      if parents.contains node then
        let newDeg := (inDegree.getD child 0) - 1
        inDegree := inDegree.insert child newDeg
        if newDeg == 0 then
          queue := queue.push child

  -- Compute ancestors in reverse topological order
  let mut ancestorMap : HashMap α (HashSet α) := {}
  for node in topoOrder.reverse do
    let mut ancs : HashSet α := {}
    if let some parents := G.parent[node]? then
      for p in parents do
        ancs := ancs.insert p
        if let some pAncs := ancestorMap[p]? then
          for a in pAncs do
            ancs := ancs.insert a
    ancestorMap := ancestorMap.insert node ancs

  return ancestorMap

/-- Remove an edge from a to b in the DAG. -/
def removeEdge (a b : α) : DAG α where
  parent := match G.parent[b]? with
    | none => G.parent
    | some parents => G.parent.insert b (parents.erase a)

/-- Compute the transitive reduction of a DAG. The transitive reduction removes
    edges that are implied by transitivity. For each edge a → b, if there exists
    an alternate path from a to b through some intermediate node, the direct edge
    is redundant and will be removed. -/
def transitiveReduction : DAG α := Id.run do
  -- Precompute ancestors for all nodes efficiently
  let ancestorMap := G.allAncestors

  let mut result := G

  for (b, parents) in G.parent do
    for a in parents do
      -- Check if there's an alternate path from a to b
      -- This happens when there exists another parent c of b such that a is an ancestor of c
      let mut hasAlternatePath := false
      for c in parents do
        if c != a then
          if let some ancestorsOfC := ancestorMap[c]? then
            if ancestorsOfC.contains a then
              hasAlternatePath := true
              break

      if hasAlternatePath then
        result := result.removeEdge a b

  return result

end DAG

def runTests : IO Unit := do
  let stderr ← IO.getStderr
  stderr.putStrLn "Running tests..."

  -- Test 1: Simple chain A → B → C
  stderr.putStrLn "Test 1: Chain graph A → B → C"
  let g1 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"

  let ancsC := g1.ancestors "C"
  assert! ancsC.contains "A" && ancsC.contains "B" && ancsC.size == 2
  stderr.putStrLn "  ✓ ancestors(C) = {A, B}"

  -- Test 2: Diamond A → B, A → C, B → D, C → D
  stderr.putStrLn "Test 2: Diamond graph"
  let g2 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"

  let ancsD := g2.ancestors "D"
  assert! ancsD.contains "A" && ancsD.contains "B" && ancsD.contains "C" && ancsD.size == 3
  stderr.putStrLn "  ✓ ancestors(D) = {A, B, C}"

  -- Test 3: allAncestors matches individual ancestors calls
  stderr.putStrLn "Test 3: allAncestors consistency"
  let allAncs := g2.allAncestors
  for node in ["A", "B", "C", "D"] do
    let expected := g2.ancestors node
    let actual := allAncs.getD node {}
    -- Check that both sets have the same elements
    assert! expected.size == actual.size
    for e in expected do
      assert! actual.contains e
  stderr.putStrLn "  ✓ allAncestors matches individual ancestors calls"

  -- Test 4: Transitive reduction removes A → C from A → B → C, A → C
  stderr.putStrLn "Test 4: Transitive reduction"
  let g3 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "B" "C"
    |>.insertEdge "A" "C"  -- This edge should be removed

  let g3reduced := g3.transitiveReduction
  -- After reduction, A should not be a parent of C
  let parentsOfC := g3reduced.parent.getD "C" {}
  assert! !parentsOfC.contains "A" && parentsOfC.contains "B" && parentsOfC.size == 1
  stderr.putStrLn "  ✓ Transitive edge A → C removed"

  -- Test 5: Diamond with transitive edges
  stderr.putStrLn "Test 5: Diamond with all edges"
  let g4 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"
    |>.insertEdge "B" "D"
    |>.insertEdge "C" "D"
    |>.insertEdge "A" "D"  -- This edge should be removed (transitive via B and C)

  let g4reduced := g4.transitiveReduction
  let parentsOfD := g4reduced.parent.getD "D" {}
  assert! !parentsOfD.contains "A" && parentsOfD.contains "B" && parentsOfD.contains "C"
  stderr.putStrLn "  ✓ Transitive edge A → D removed in diamond"

  -- Test 6: No false removals
  stderr.putStrLn "Test 6: Non-transitive edges preserved"
  let g5 : DAG String := DAG.empty
    |>.insertEdge "A" "B"
    |>.insertEdge "A" "C"

  let g5reduced := g5.transitiveReduction
  -- Both edges should remain (neither is transitive)
  let parentsOfB := g5reduced.parent.getD "B" {}
  let parentsOfC := g5reduced.parent.getD "C" {}
  assert! parentsOfB.size == 1 && parentsOfB.contains "A"
  assert! parentsOfC.size == 1 && parentsOfC.contains "A"
  stderr.putStrLn "  ✓ Non-transitive edges preserved"

  stderr.putStrLn "All tests passed! ✓"

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
  | ["test"] =>
    runTests
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
    for (a,bs) in G.parent do for b in bs do
      println! s!"{a} -> {b}"
  | _ =>
    throw <| .userError "Usage: RefactorGraph <name> or RefactorGraph test"

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

def ancestors (a : α) : HashSet α := Id.run do
  let mut visited : HashSet α := {}
  let mut worklist : Array α := #[]
  if let some parents := G.parent[a]? then
    for p in parents do
      worklist := worklist.push p
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

def allAncestors : HashMap α (HashSet α) := Id.run do
  let mut inDegree : HashMap α Nat := {}
  for (node, parents) in G.parent do
    inDegree := inDegree.insert node parents.size
    for p in parents do
      if !inDegree.contains p then
        inDegree := inDegree.insert p 0
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
    for (child, parents) in G.parent do
      if parents.contains node then
        let newDeg := (inDegree.getD child 0) - 1
        inDegree := inDegree.insert child newDeg
        if newDeg == 0 then
          queue := queue.push child
  let mut ancestorMap : HashMap α (HashSet α) := {}
  for node in topoOrder do
    let mut ancs : HashSet α := {}
    if let some parents := G.parent[node]? then
      for p in parents do
        ancs := ancs.insert p
        if let some pAncs := ancestorMap[p]? then
          for a in pAncs do
            ancs := ancs.insert a
    ancestorMap := ancestorMap.insert node ancs

  return ancestorMap

def descendants (b : α) : HashSet α := Id.run do
  let ancs := G.allAncestors
  let mut descs : HashSet α := {}
  for (a, s) in ancs do
    if s.contains b then do
      descs := descs.insert a
  return descs

def removeEdge (a b : α) : DAG α where
  parent := match G.parent[b]? with
    | none => G.parent
    | some parents => G.parent.insert b (parents.erase a)

def nodes : HashSet α := Id.run do
  let mut result : HashSet α := {}
  for (node, parents) in G.parent do
    result := result.insert node
    for p in parents do
      result := result.insert p
  return result

def leaves : HashSet α := Id.run do
  let mut hasChildren : HashSet α := {}
  for (_, parents) in G.parent do
    for p in parents do
      hasChildren := hasChildren.insert p
  let mut result : HashSet α := {}
  for node in G.nodes do
    if !hasChildren.contains node then
      result := result.insert node
  return result

def removeNode (a : α) : DAG α := Id.run do
  let mut newParent : HashMap α (HashSet α) := {}
  for (node, parents) in G.parent do
    if node != a then
      let filteredParents := parents.erase a
      if filteredParents.size > 0 then
        newParent := newParent.insert node filteredParents
  return { parent := newParent }

def removeNodes (nodes : HashSet α) : DAG α := Id.run do
  let mut result := G
  for node in nodes do
    result := result.removeNode node
  return result

def transitiveReduction : DAG α := Id.run do
  let ancestorMap := G.allAncestors
  let mut result := G
  for (b, parents) in G.parent do
    for a in parents do
      if a == b then
        result := result.removeEdge a b
      else
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

def dot [ToString α] : String := Id.run do
  let mut result := "digraph G {\n"

  for node in G.nodes do
    result := result ++ s!"  \"{toString node}\";\n"

  for (child, parents) in G.parent do
    for parent in parents do
      result := result ++ s!"  \"{toString parent}\" -> \"{toString child}\";\n"

  result := result ++ "}"
  return result

end DAG

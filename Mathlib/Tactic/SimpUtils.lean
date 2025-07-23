import Mathlib.Init
import Lean.Elab.Tactic.Simproc


/-! # Simp Theorem Utilities

This file implements some commands to print out simprocs/dsimprocs/simp theorems that match
a given pattern.

-/

open Lean Elab Meta Command Simp DiscrTree

open DiscrTree

/-- Outputs all the elements that lie within a node of the DiscTree. -/
partial def Lean.Meta.DiscrTree.Trie.flatten {α} : Trie α → Array α
  | node (vs : Array α) (children : Array (Key × Trie α)) =>
    vs ++ (children.map fun (_, trie) ↦ trie.flatten).flatten

/-- Output all elements in a DiscTree that match on a given key. -/
def Lean.Meta.DiscrTree.getAllFromKey {α : Type} (tree : DiscrTree α)
    (key : Key) : Array α :=
  match tree.root.find? key with
  | some trie => trie.flatten
  | none => #[]

/-- Get all simprocs in the environment that match a pattern in an array of keys. -/
def simprocFromKeys (keys : Array SimpTheoremKey) (dsimprocOnly := false) :
    CoreM <| Array SimprocEntry := do
  let simprocs ← Simp.getSimprocs
  let preMatches := (keys.map fun key ↦ simprocs.pre.getAllFromKey key).flatten
  let postMatches := (keys.map fun key ↦ simprocs.post.getAllFromKey key).flatten
  let mut out := preMatches ++ postMatches
  if dsimprocOnly then
    -- Filter to keep only dsimprocs.
    out := out.filter fun simprocEntry ↦ simprocEntry.proc.isRight
  return out

/-- Print out an array of simprocs, providing the name and the docstring. -/
def printSimprocList (simprocs : Array SimprocEntry) : CoreM String := do
  let env ← getEnv
  let out ← simprocs.mapM fun simprocEntry ↦ do
    let declName := simprocEntry.declName
    let docString := (← Lean.findDocString? env declName).getD ""
    return s!"{simprocEntry.declName}:\n{docString}"
  return "\n\n\n".intercalate out.toList

/-- Get all simp theorems in the environment that match a pattern in an array of keys. -/
def simpTheoremsFromKeys (keys : Array SimpTheoremKey) : CoreM <| Array SimpTheorem := do
  let simpTheorems ← Lean.Meta.getSimpTheorems
  let preMatches := (keys.map fun key ↦ simpTheorems.pre.getAllFromKey key).flatten
  let postMatches := (keys.map fun key ↦ simpTheorems.post.getAllFromKey key).flatten
  let out := preMatches ++ postMatches
  return out

/-- Print out an array of simp theorems, providing the name. -/
def printSimpTheoremList (simpThms : Array SimpTheorem) : MetaM String := do
  let out ← simpThms.filterMapM fun simpThm ↦ do
    match simpThm.origin with
      | .decl declName _ _ =>
        let decl ← Lean.getConstInfo declName
        return s!"{declName} :  {← ppExpr decl.type}"
      | _ => return none
  return "\n\n".intercalate out.toList

/-- Print all simprocs that match a given pattern. -/
elab "#simprocs " t:term : command => liftTermElabM do
  let keys ← elabSimprocKeys t
  let simprocs ← simprocFromKeys keys
  let out ← printSimprocList simprocs
  Lean.logInfo out

/-- Print all dsimprocs that match a given pattern. -/
elab "#dsimprocs " t:term : command => liftTermElabM do
  let keys ← elabSimprocKeys t
  let simprocs ← simprocFromKeys keys true
  let out ← printSimprocList simprocs
  Lean.logInfo out

/-- Print all simp theorems that match a given pattern. -/
elab "#simp_theorems" t:term : command => liftTermElabM do
  let keys ← elabSimprocKeys t
  let simpThms ← simpTheoremsFromKeys keys
  let out ← printSimpTheoremList simpThms
  Lean.logInfo out

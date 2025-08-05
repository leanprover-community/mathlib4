/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Mathlib.Init
import Lean.Elab.Tactic.Simproc

/-! # Simp Theorem Utilities

This file implements some commands to print out simprocs/dsimprocs/simp theorems that match
a given pattern.

-/

open Lean Elab Meta Command Simp DiscrTree

open DiscrTree

/-- Outputs all the elements that lie within a node of the DiscTree. -/
partial def Lean.Meta.DiscrTree.Trie.flattenWithKey {α} : Trie α → Array α
  | node (vs : Array α) (children : Array (Key × Trie α)) =>
    (vs.map fun a ↦ a) ++ (children.map fun trie ↦ trie.snd.flattenWithKey).flatten

/-- Output all elements in a DiscTree that match on a given key. -/
def Lean.Meta.DiscrTree.getAllFromKey {α : Type} (tree : DiscrTree α) (key : Key) : Array α :=
  match tree.root.find? key with
  | some trie => trie.flattenWithKey
  | none => #[]

-- TODO(Paul-Lez): maybe this should be in Core?
private def Lean.PersistentHashMap.toHashMap {α β}
    {_ : BEq α} {_ : Hashable α} (m : PersistentHashMap α β) : Std.HashMap α β :=
  m.foldl (init := {}) fun ps k v => ps.insert k v

private structure SimprocData where
  declName : Name
  isRegistered : Bool
  isDSimproc : Bool
deriving BEq

private def getSimprocsAsArray : CoreM (Array Name) := do
  let currentSimprocs ← getSimprocs
  let currentSimprocsAsArray := currentSimprocs.pre.toArray ++ currentSimprocs.post.toArray
  return currentSimprocsAsArray.map fun simprocEntry ↦ simprocEntry.snd.declName

/-- Get all simprocs in the environment and output a `DiscrTree Name` structure.

Note: this does not distinguish between pre and post procedures! -/
private def getAllSimprocs : CoreM (DiscrTree SimprocData) := do
  let env ← getEnv
  let state := simprocDeclExt.getState env
  let currentSimprocs ← getSimprocsAsArray
  let mut simprocs : DiscrTree SimprocData := {}
  for (simprocName, simprocKeys) in state.builtin.union state.newEntries.toHashMap do
    unless ← hasConst simprocName do continue
    simprocs := simprocs.insertCore simprocKeys
      ⟨simprocName, currentSimprocs.contains simprocName, ← checkSimprocType simprocName⟩
  return simprocs

/-- Get all simprocs in the environment that match a pattern in an array of keys. -/
def simprocFromKeys (keys : Array SimpTheoremKey) (simprocs : DiscrTree SimprocData)
    (dsimprocOnly := false) : CoreM <| Array SimprocData := do
  let simprocMatches := (keys.map fun key ↦ simprocs.getAllFromKey key).flatten
  let mut out := simprocMatches
  if dsimprocOnly then
    -- Filter to keep only dsimprocs.
    out := out.filter fun simprocEntry ↦ simprocEntry.isDSimproc
  return out

private def simprocOutStr (simprocData : SimprocData) (keys : Array Key) (doc : String) :
    CoreM MessageData := do
  let dproc := if simprocData.isDSimproc then "simproc" else "dsimproc"
  let cmd := if simprocData.isRegistered then m!"" else m!"_decl"
  let doc := if doc == "" then m!"" else m!"/--\n{doc}\n-/\n"
  let keys := m!"({← keysAsPattern keys})"
  let fullCmd := doc ++ dproc ++ cmd ++ m!" {simprocData.declName} " ++ keys
  return fullCmd

/-- Print out an array of simprocs, providing the name and the docstring. -/
def printSimprocList (simprocs : Array SimprocData) : MetaM MessageData := do
  let env ← getEnv
  let out ← simprocs.filterMapM fun simprocName ↦ do
    let keys := (← getSimprocDeclKeys? simprocName.declName).getD #[]
    let doc := (← Lean.findDocString? env simprocName.declName).getD ""
    return ← simprocOutStr simprocName keys doc
  return m!"\n\n".joinSep out.toList

/-- Get all simp theorems in the environment that match a pattern in an array of keys. -/
def simpTheoremsFromKeys (keys : Array SimpTheoremKey) : CoreM <| Array  SimpTheorem  := do
  let simpTheorems ← Lean.Meta.getSimpTheorems
  let preMatches := (keys.map fun key ↦ simpTheorems.pre.getAllFromKey key).flatten
  let postMatches := (keys.map fun key ↦ simpTheorems.post.getAllFromKey key).flatten
  let out := preMatches ++ postMatches
  return out

/-- Print out an array of simp theorems, providing the name. -/
def printSimpTheoremList (simpThms : Array SimpTheorem) : MetaM MessageData := do
  let out ← simpThms.filterMapM fun simpThm ↦ do
    match simpThm.origin with
    | .decl declName _ _ =>
      let decl ← Lean.getConstInfo declName
      let keys := (← getSimprocDeclKeys? declName).getD #[]
      return m!"{declName} : {← keysAsPattern keys}\n{← ppExpr decl.type}"
    | _ => return none
  return m!"\n\n".joinSep out.toList

/-- Print all simprocs that match a given pattern. -/
elab "#simprocs " t:term : command => liftTermElabM do
  let keys ← elabSimprocKeys t
  let simprocs ← simprocFromKeys keys (← getAllSimprocs)
  let out ← printSimprocList simprocs
  Lean.logInfo out

/-- Print all dsimprocs that match a given pattern. -/
elab "#dsimprocs " t:term : command => liftTermElabM do
  let keys ← elabSimprocKeys t
  let simprocs ← simprocFromKeys keys (← getAllSimprocs) true
  let out ← printSimprocList simprocs
  Lean.logInfo out

/-- Print all simp theorems that match a given pattern. -/
elab "#simp_theorems" t:term : command => liftTermElabM do
  let keys ← elabSimprocKeys t
  let simpThms ← simpTheoremsFromKeys keys
  let out ← printSimpTheoremList simpThms
  Lean.logInfo out

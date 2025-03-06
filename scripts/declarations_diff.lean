import Lean
--import Batteries -- technically not needed, since `Mathlib` already imports it
--import Mathlib
--import Archive
--import Counterexamples

open Lean

local instance : ToString NameSet where
  toString ns := s!"{ns.toArray.qsort (·.toString < ·.toString)}"

/--
Prints each declaration in the environment that is not an internal detail.

CI uses the name of this command: if you change it, make sure to update the CI configuration.
-/
elab "#all_declarations " branch:str : command => do
  let mut sorted : Array String := ∅
  for (nm, _) in (← getEnv).constants do
    if !nm.isInternalDetail then
      sorted := sorted.binInsert (· < ·) nm.toString
  dbg_trace "* Writing {sorted.size} declarations to '{branch.getString}'"
  IO.FS.writeFile branch.getString <| .intercalate "\n" sorted.toList

def toUserNameSet (env : Environment) : NameSet :=
  env.constants.fold (init := ∅) (fun tot nm _ =>
    if nm.isInternalDetail then tot else tot.insert nm)

def declsFromImports (imports : Array Import) : IO NameSet := do
  let env1 ← importModules imports {}
  pure <| toUserNameSet env1

def symmDiff (e1 e2 : NameSet) : NameSet × NameSet :=
  (e1.fold (init := (∅, e2)) fun (e1, e2) n =>
    if e2.contains n then (e1, e2.erase n) else (e1.insert n, e2))

elab "ddiff" : command => do
  let mods : Array Import := #[`Mathlib.Algebra.Quandle]
  let fname : System.FilePath := "Mathlib"/"Algebra" / "Quandle.lean"
  let e1 ← declsFromImports mods
  dbg_trace "git checkout master"
  let _ ← IO.Process.run {cmd := "git", args := #["checkout", "master"]}
  dbg_trace "lake build {mods[0]}"
  let _ ← IO.Process.run {cmd := "lake", args := #["build", mods[0]]}
  let e2 ← declsFromImports mods
  let (d1, d2) := symmDiff e1 e2
  logInfo m!"{(d1, d2)}"

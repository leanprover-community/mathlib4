import Lean
--import Batteries -- technically not needed, since `Mathlib` already imports it
--import Mathlib
--import Archive
--import Counterexamples

open Lean

def NStoString (ns : NameSet) : String :=
  let sorted := ns.fold (init := #[]) fun tot n => tot.binInsert (·.toString < ·.toString) n
  s!"{sorted}"
  --s!"{ns.toArray.qsort (·.toString < ·.toString)}"

local instance : ToString NameSet where
  toString := NStoString

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
  let env1 ← importModules (leakEnv := true) imports {}
  pure <| toUserNameSet env1

def symmDiff (e1 e2 : NameSet) : NameSet × NameSet :=
  (e1.diff e2, e2.diff e1)
  --(e1.fold (init := (∅, e2)) fun (e1, e2) n =>
  --  if e2.contains n then (e1, e2.erase n) else (e1.insert n, e2))

elab "ddiff" : command => do
  let mods : Array Import := #[`Mathlib.Algebra.Quandle]
  let fname : System.FilePath := "Mathlib" / "Algebra" / "Quandle.lean"

  let m1 ← IO.Process.run {cmd := "lake", args := #["exe", "cache", "get", fname.toString]}
  dbg_trace "m1: '{m1}'"

  --let m2 ← IO.Process.run {cmd := "lake", args := #["build", toString mods[0]]}
  --dbg_trace "m2: '{m2}'"
  let e1 ← declsFromImports mods
  dbg_trace "Found {e1.size} declarations"

  dbg_trace "git checkout master {fname.toString}"
  let m3 ← IO.Process.run {cmd := "git", args := #["checkout", "master", fname.toString]}
  dbg_trace "m3: '{m3}'"
  --dbg_trace "git checkout master Mathlib"
  --let m3 ← IO.Process.run {cmd := "git", args := #["checkout", "master", "Mathlib"]}
  --dbg_trace "m3: '{m3}'"

  dbg_trace "lake exe cache get {fname.toString}"
  let m4 ← IO.Process.run {cmd := "lake", args := #["exe", "cache", "get", fname.toString]}
  dbg_trace "m4: '{m4}'"

  --dbg_trace "lake build {mods[0]}"
  --let m5 ← IO.Process.run {cmd := "lake", args := #["build", "--no-build", toString mods[0]]}
  --dbg_trace "m5: '{m5}'"

  let e2 ← declsFromImports mods
  dbg_trace "Found {e2.size} declarations"
  --let (d1, d2) := symmDiff e1 e2
--  let e2 := (e2.erase `Nat).insert `NewNat
--  logInfo m!"{(NStoString <| e1.diff e2, NStoString <| e2.diff e1)}"
  logInfo m!"{(e1.diff e2).toArray}, {(e2.diff e1).toArray}"
  --logInfo m!"{(d1, d2)}"

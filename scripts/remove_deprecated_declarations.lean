/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib --.Deprecated.Order

/-!
d
-/

open Lean Elab Command

structure DeprecationInfo where
  module : Name
  rgStart : Position
  rgStop : Position
  since : String

def getDeprecatedInfo (nm : Name) (verbose? : Bool) :
    CommandElabM (Option DeprecationInfo) := do
  let env ← getEnv
  -- if there is a `since` in the deprecation
  if let some {since? := some since, ..} := Linter.deprecatedAttr.getParam? env nm
  then
    -- retrieve the `range` for the declaration
    if let some {range := rg, ..} ← findDeclarationRanges? nm
    then
      -- retrieve the module where the declaration is located
      if let some mod ← findModuleOf? nm
      then
        if verbose? then
          logInfo
            s!"In the module '{mod}', the declaration {nm} at {rg.pos}--{rg.endPos} \
              is deprecated since {since}"
        return some {module := mod, rgStart := rg.pos, rgStop := rg.endPos, since := since}
  return none

def cleanUpRanges (fin : Array String.Range) : Array String.Range :=
  fin.foldl (init := #[]) fun tot n =>
    if let some back := tot.back? then
      if back.start ≤ n.start && n.stop ≤ back.stop then
        tot.pop.push n
      else
        tot.push n
    else
        tot.push n

def deprecatedHashMap (deprecateFrom : String) :
    CommandElabM (Std.HashMap String (Array String.Range)) := do
  let mut fin := ∅
  for (nm, _) in (← getEnv).constants.map₁ do
    if let some ⟨modName, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      if modName.getRoot != `Mathlib then continue
      if deprecateFrom < since then
        continue
      let lean ← findLean (← getSrcSearchPath) modName
      let file ← IO.FS.readFile lean
      let fm := FileMap.ofString file
      let rg : String.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
      fin := fin.alter lean.toString fun a =>
        (a.getD #[⟨fm.positions.back!, default⟩]).binInsert (·.1 < ·.1) rg
  return fin

def removeDeprecations (fname : String) (rgs : Array String.Range) : IO String := do
  let file ← IO.FS.readFile fname
  let mut curr : String.Pos := 0
  let mut fileSubstring := file.toSubstring
  let mut tot := ""
  for next in rgs do
    if next.start < curr then continue
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring := ({fileSubstring with startPos := next.stop}.dropWhile (!·.isWhitespace)).trimLeft
  return tot

open Lean Elab Command in
elab "#remove_deprecated_declarations " date:str really?:("really")? : command => do
  let deprecateFrom := date.getString
  let dmap ← deprecatedHashMap deprecateFrom
  dbg_trace "{dmap.fold (init := 0) fun tot _ rgs => tot + rgs.size} deprecations among {dmap.size} files"
  for (mod, rgs) in dmap.toArray.qsort (·.1 < ·.1) do
    let mod1 := "Mathlib" ++ (mod.splitOn "Mathlib").getLast!
    let rgs := cleanUpRanges rgs
    dbg_trace "From '{mod1}' remove\n{rgs.map fun | ⟨a, b⟩ => (a, b)}\n---\n{← removeDeprecations mod rgs}"
    let num := rgs.size - 1
    dbg_trace "remove {num} declaration{if num == 1 then " " else "s"} from '{mod1}'"
    if really?.isSome then
      IO.FS.writeFile mod (← removeDeprecations mod rgs)

#remove_deprecated_declarations "2025-02-31" --really
/--
info: import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module (since := "2025-09-02")

whatsnew in
whatsnew in
theorem NotDeprecated : True := trivial
-/
#guard_msgs in
run_cmd
  let modName : Name := `Mathlib.Deprecated.Order
  let deprecateFrom := "2025-09-02"
  let dmap ← deprecatedHashMap deprecateFrom
  let lean ← findLean (← getSrcSearchPath) modName
  let file ← IO.FS.readFile lean
  for (d, rgs) in dmap do
    if d != file then continue
    else
/-
  let fm := FileMap.ofString file
  --dbg_trace file

  let mut rgs := #[]
  --for nm in #[``X, ``Y, ``Z, ``NotDeprecated] do
  for (nm, _) in (← getEnv).constants.map₁ do
    --if nm == ``X then dbg_trace "found {nm}"
    if let some ⟨mod, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      if mod != modName then
        --if nm == ``X then dbg_trace "wrong mod {mod}"
        continue
      if since < deprecateFrom then
        --if nm == ``X then dbg_trace "wrong since {since}"
        continue
      let rg : String.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
      rgs := rgs.binInsert (·.1 < ·.1) rg
  --dbg_trace rgs.size
  --dbg_trace rgs.map fun | {start := a, stop := b} => (a, b)
  --let rgs : Array String.Range := #[]
  rgs := rgs.push (⟨fm.positions.back!, default⟩)
-/
  let mut curr : String.Pos := 0
  let mut fileSubstring := file.toSubstring
  let mut tot := ""
  for next in rgs do
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring := {fileSubstring with startPos := next.stop}.trimLeft
  dbg_trace tot



run_cmd
  for nm in #[``X, ``Y, ``Z] do
    let ⟨mod, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm true
#eval do
  findLean (← getSrcSearchPath) `Mathlib.Deprecated.Order

#check findModuleOf?

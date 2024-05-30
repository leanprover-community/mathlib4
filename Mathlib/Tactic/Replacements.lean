/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.ReplaceRefine

/-!
This file contains the code to perform the replacements that the `ReplaceRefine` linter
outputs.
-/

/--
info: [("refine'", "refine") beginning (19, 2), ("_", "?_") beginning (19, 11), ("_", "?_") beginning (19, 14)]
-/
--#guard_msgs in
example : True ∧ True := by
  refine' ⟨_, _⟩
  trivial
  trivial

/--
info: [("refine'", "refine") beginning (28, 2), ("_", "?_") beginning (28, 11), ("_", "?_") beginning (28, 14)]
-/
--#guard_msgs in
instance (priority := 1) fine : True ∧ True := by
  refine' ⟨_, _⟩
  trivial
  trivial

/-
info: [replace refine' with refine between (47, 2) and (47, 9),
 replace _ with ?_ between (0, (47, 11)) and (0, (47, 12)),
 replace _ with ?_ between (0, (47, 14)) and (0, (47, 15))]
-/
--#guard_msgs in
/-- docs -/
@[simp]
partial
def oh : Nat × Nat := by
  refine' ⟨_, _⟩
  exact 0
  exact 0

def String.replaceCheck (s check repl : String) (st : Nat) : String :=
  let sc := s.toList
  let fi := st + check.length
  if (sc.take fi).drop st == check.toList then
    ⟨sc.take st ++ repl.toList ++ sc.drop fi⟩
  else
    dbg_trace "{check} not replaced with {repl} in {(st, fi)}"
    s

/-- info: true -/
#guard_msgs in
#eval
  let str := "  refine' ⟨_, _⟩"
  str.replaceCheck "_" "?_" 11 == "  refine' ⟨?_, _⟩"

/-- info: true -/
#guard_msgs in
#eval
  let str := "  refine' ⟨_, _⟩"
  str.replaceCheck "" "?" 11 == "  refine' ⟨?_, _⟩"

/-- info: true -/
#guard_msgs in
#eval
  let str := "  refine' ⟨_, _⟩"
  str.replaceCheck "refine'" "refine" 2 == "  refine ⟨_, _⟩"

/-- info: true -/
#guard_msgs in
#eval
  let str := "  refine' ⟨_, _⟩"
  str.replaceCheck "'" "" 8 == "  refine ⟨_, _⟩"

/-- inserts the string `plus` at position `n` in the string `s`.
It has a bespoke test for checking that we only add `plus` before a `_`. -/
def String.insert (s : String) (n : Nat) (plus : String) : String :=
  let sc := s.toList
  if sc.getD n default == '_' then
    ⟨sc.take n ++ plus.toList ++ sc.drop n⟩
  else dbg_trace "not inserted"; s

/-- info: true -/
#guard_msgs in
#eval
  let str := "  refine' ⟨_, _⟩"
  let plus := "?"
  let n := 11
  "  refine' ⟨?_, _⟩" == str.insert n plus

/-- erases the string `m` characters starting from position `n` in the string `s`.
It has a bespoke test for checking that we only remove the final `'` from `refine'`. -/
def String.erase (s : String) (n m : Nat) : String :=
  let sc := s.toList
  let check := (sc.take (n + m)).drop (n - 6)
  if check == "refine'".toList then
    ⟨sc.take n ++ sc.drop (n + m)⟩
  else dbg_trace "not erased"; s

/-- info: true -/
#guard_msgs in
#eval
  let str := "  refine' ⟨_, _⟩"
  let n := 2
  let m := 1
  "  refine ⟨_, _⟩" == str.erase (n + 6) m

/-- `substitutions lines dat` takes as input the array `lines` of strings and the "instructions"
`dat : Array (Nat × Nat × Nat)`.
The elements of `dat` are of the form `(0/1, l, c)` where
* `(1, l, c)` means that we remove a `'` from `refine'` on line `l` and column `c+6`;
* `(0, l, c)` means that we add a `?` before a `_` on line `l` and column `c`.
-/
def substitutions (lines : Array String) (dat : Array ((String × String) × (Nat × Nat))) : Array String := Id.run do
  let mut new := lines
  for ((check, repl), (l', c)) in dat do
    let l := l' - 1
    let newLine :=  new[l]!.replaceCheck check repl c
    new := new.modify l (fun _ => newLine)
  new

/-- `getBuild` checks if there is an available cache.  If this is the case, then it returns
the replayed build, otherwise it asks to build/download the cache. -/
def getBuild : IO (Array String) := do
  let build ← IO.Process.output { cmd := "lake", args := #["build", "--no-build"] }
  if build.exitCode != 0 then
    IO.println "There are out of date oleans. Run `lake build` or `lake exe cache get` first"
    return default
  return (build.stdout.splitOn "\n").toArray

open Lean

section parsers

open System.FilePath in
/-- `parseFile fil` converts the syntax `fil` into a `System.FilePath` -/
partial
def parseFile : TSyntax `term → System.FilePath
  | `($xs/$x:ident) =>
      let id := x.getId.toString
      parseFile xs / match id.splitOn ⟨[extSeparator]⟩ with
                      | [fil, "lean"] => addExtension fil "lean"
                      | [f] => f
                      | _ => default
  | `($id:ident) => id.getId.toString
  | _ => default

/-- `parseCorrections xs` converts the syntax `xs` into a `#[(a₁, b₁, c₁), ..., (aₙ, bₙ, cₙ)]`. -/
def parseCorrections : TSyntax `term → Array (Nat × Nat × Nat)
  | `([$xs,*]) => Id.run do
    let mut corrections := #[]
    for x in xs.getElems do
      let new := match x with
        | `(($a:num, ($b:num, $c:num))) => (a.getNat, b.getNat, c.getNat)
        | _ => default
      corrections := corrections.push new
    return corrections.qsort fun (_, l1, c1) (_, l2, c2) => l1 > l2 || (l1 == l2 && c1 > c2)
  | _ => default
end parsers

section syntax_and_elabs
/-- a custom syntax category for parsing the output of `lake build`. -/
declare_syntax_cat build

/-- a successfully built file. -/
syntax &"ℹ" "[" num "/" num "]" ident ident : build

/-- a file reporting some information. -/
syntax &"info:" "././././" term &".lean" ":" num ":" num ":" term : build

/-- a file reporting some information. -/
syntax &"info:" "././././" term &".lean" ":" num ":" num ":" build : build

/-- a declaration containing too many holes. -/
syntax &"info:" "stderr:" many(num"is too many holes!") : build

/-- do nothing on a declaration containing too many holes. -/
elab "info:" "stderr:" _t:many(num"is too many holes!") : command => return

/-- a successfully built project. -/
syntax &"Build completed successfully." : build

syntax "(" str "," str ")" &"beginning" "(" num "," num ")" : build
syntax "[" build,* "]" : build

#check `(build| [
  ("refine'", "refine") beginning (19, 2),
  ("_", "?_") beginning (19, 11),
  ("_", "?_") beginning (19, 14)
])

def parseRepls : TSyntax `build → Array ((String × String) × Nat × Nat)
  | `(build| [ $rs,* ]) =>
    rs.getElems.map fun r => match r with
      | `(build| ($curr:str, $repl:str) beginning ($row:num, $col:num) ) =>
        ((curr.getString, repl.getString), row.getNat, col.getNat)
      | _ => default
  | _ => default

#eval show CoreM _ from do
  let bld ← `(build| [
    ("refine'", "refine") beginning (19, 2),
    ("_", "?_") beginning (19, 11),
    ("_", "?_") beginning (19, 14)])
  let arr := parseRepls bld
  IO.println arr

elab "read " bld:build : command => do
  let arr := parseRepls bld
  logInfo m!"{arr}"

read [
  ("refine'", "refine") beginning (19, 2),
  ("_", "?_") beginning (19, 11),
  ("_", "?_") beginning (19, 14)
]


/-- do nothing on a successfully built file. -/
elab "ℹ [" num "/" num "]" ident ident : command => return
/-- do nothing on a successfully built project. -/
elab "Build completed successfully." : command => logInfo "All done!"

elab "info:" "././././" t1:term ":" num ":" num ":" t:build : command => do
  let file : System.FilePath := parseFile t1
  let corrections : Array ((String × String) × (Nat × Nat)) := parseRepls t
  let newContent := "\n".intercalate
    ((substitutions (← IO.FS.lines file) corrections)).toList
  logInfo newContent

/-
set_option linter.unusedVariables false in
/-- extract the file name, the array of corrections, perform them and rewrite the file. -/
elab "info:" "././././" t1:term ":" num ":" num ":" t:term : command => do
  let file : System.FilePath := parseFile t1
  let corrections : Array (Nat × Nat × Nat) := parseCorrections t
  let newContent := "\n".intercalate
    ((substitutions (← IO.FS.lines file) corrections)).toList
  --IO.FS.writeFile file (newContent.trimRight ++ "\n")
-/

end syntax_and_elabs

/-
lake exe cache get
tgt='buildOutput.lean'
printf 'import Mathlib.Tactic.Replacements\n\n' > "${tgt}"
lake build >> "${tgt}"

-/

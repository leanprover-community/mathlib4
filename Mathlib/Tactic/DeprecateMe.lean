/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Meta.Tactic.TryThis
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Lemma

/-!
#  `deprecate to` -- a deprecation tool

Writing
```lean
deprecate to new_name new_name₂ ... new_nameₙ
theorem old_name : True := .intro
```
where `new_name new_name₂ ... new_nameₙ` is a sequence of identifiers produces the
`Try this` suggestion:
```lean
theorem new_name : True := .intro

@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name

@[deprecated (since := "YYYY-MM-DD")] alias old_name₂ := new_name₂
...

@[deprecated (since := "YYYY-MM-DD")] alias old_nameₙ := new_nameₙ
```
where `old_name old_name₂ ... old_nameₙ` are the non-blacklisted declarations
(auto)generated by the initial command.

TODO:
* the "new" names come fully qualified with their namespace -- if the deprecation is happening
  inside a `namespace X`, it would be better to remove the `X` prefix from them;
* preserve formatting of existing command?
-/

namespace Mathlib.Tactic.DeprecateMe

open Lean Elab Term Command

/-- Produce the syntax for the command `@[deprecated (since := "YYYY-MM-DD")] alias n := id`. -/
def mkDeprecationStx (id : TSyntax `ident) (n : Name) (dat : Option String := none) :
    CommandElabM (TSyntax `command) := do
  let dat := ← match dat with
                | none => IO.Process.run { cmd := "date", args := #["-I"] }
                | some s => return s
  let nd := mkNode `str #[mkAtom ("\"" ++ dat.trimRight ++ "\"")]
  `(command| @[deprecated (since := $nd)] alias $(mkIdent n) := $id)

/-- Returns the array of names that are in `new` but not in `old`. -/
def newNames (old new : Environment) : Array Name := Id.run do
  let mut diffs := #[]
  for (c, _) in new.constants.map₂.toList do
    unless old.constants.map₂.contains c do
      diffs := diffs.push c
  pure <| diffs.qsort (·.toString < ·.toString)

variable (newName : TSyntax `ident) in
/--
If the input command is a `theorem` or a `lemma`, then it replaces the name of the
resulting declaration with `newName` and it returns the old declaration name and the
command with the new name.

If the input command is neither a `theorem` nor a `lemma`, then it returns
`.missing` and the unchanged command.
-/
def renameTheorem : TSyntax `command → TSyntax `Lean.Parser.Command.declId × TSyntax `command
  | `(command| $dm:declModifiers theorem $id:declId $d:declSig $v:declVal) => Unhygienic.run do
    return (id, ← `($dm:declModifiers theorem $newName:declId $d:declSig $v:declVal))
  | `(command| $dm:declModifiers lemma $id:declId $d:declSig $v:declVal) => Unhygienic.run do
    return (id, ← `($dm:declModifiers lemma $newName:declId $d:declSig $v:declVal))
  | a => (default, a)

open Meta.Tactic.TryThis in
/--
Writing
```lean
deprecate to new_name new_name₂ ... new_nameₙ
theorem old_name : True := .intro
```
where `new_name new_name₂ ... new_nameₙ` is a sequence of identifiers produces the
`Try this` suggestion:
```lean
theorem new_name : True := .intro

@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name

@[deprecated (since := "YYYY-MM-DD")] alias old_name₂ := new_name₂
...

@[deprecated (since := "YYYY-MM-DD")] alias old_nameₙ := new_nameₙ
```
where `old_name old_name₂ ... old_nameₙ` are the non-blacklisted declarations
(auto)generated by the initial command.

The "YYYY-MM-DD" entry is today's date and it is automatically filled in.

`deprecate to` makes an effort to match `old_name`, the "visible" name, with
`new_name`, the first identifier produced by the user.
The "old", autogenerated declarations `old_name₂ ... old_nameₙ` are retrieved in alphabetical order.
In the case in which the initial declaration produces at most 1 non-blacklisted
declarations besides itself, the alphabetical sorting is irrelevant.

Technically, the command also take an optional `String` argument to fill in the date in `since`.
However, its use is mostly intended for debugging purposes, where having a variable date would
make tests time-dependent.
-/
elab tk:"deprecate to " id:ident* dat:(str)? ppLine cmd:command : command => do
  let oldEnv ← getEnv
  try
    elabCommand cmd
  finally
    let newEnv ← getEnv
    let allNew := newNames oldEnv newEnv
    let skip ← allNew.filterM (·.isBlackListed)
    let mut news := allNew.filter (! · ∈ skip)
    let mut warn := #[]
    if id.size < news.size then
      warn := warn.push s!"Un-deprecated declarations: {news.toList.drop id.size}"
    if news.size < id.size then
      for i in id.toList.drop news.size do logErrorAt i ""
      warn := warn.push s!"Unused names: {id.toList.drop news.size}"
    let (oldId, newCmd) := renameTheorem id[0]! cmd
    let oldNames := ← resolveGlobalName (oldId.raw.getArg 0).getId.eraseMacroScopes
    let fil := news.filter fun n => n.toString.endsWith oldNames[0]!.1.toString
    if fil.size != 1 && oldId != default then
      logError m!"Expected to find one declaration called {oldNames[0]!.1}, found {fil.size}"
    if oldId != default then
      news := #[fil[0]!] ++ (news.erase fil[0]!)
    let pairs := id.zip news
    let msg := s!"* Pairings:\n{pairs.map fun (l, r) => (l.getId, r)}" ++
      if skip.size != 0 then s!"\n\n* Ignoring: {skip}" else ""
    let dat := if dat.isSome then some dat.get!.getString else none
    let stxs ← pairs.mapM fun (id, n) => mkDeprecationStx id n dat
    if newCmd == cmd then
      logWarningAt cmd m!"New declaration uses the old name {oldId.raw.getArg 0}!"
    let stxs := #[newCmd] ++ stxs
    if warn != #[] then
      logWarningAt tk m!"{warn.foldl (· ++ "\n" ++ ·) "Warnings:\n"}"
    liftTermElabM do
      let prettyStxs ← stxs.mapM (SuggestionText.prettyExtra <|.tsyntax ·)
      let toMessageData := (prettyStxs.toList.drop 1).foldl
        (fun x y => x ++ "\n\n" ++ y) prettyStxs[0]!

      addSuggestion (header := msg ++ "\n\nTry this:\n") (← getRef)
        toMessageData

end Mathlib.Tactic.DeprecateMe

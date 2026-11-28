/-
Copyright (c) 2026 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Snir Broshi, Jovan Gerbscheid
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Linter.Deprecated
public meta import Lean.Linter.EnvLinter.Basic
public meta import Lean.Meta.Instances
public meta import Lean.OriginalConstKind
public meta import Lean.Parser.Term.Doc
public meta import Std.Data.HashMap.AdditionalOperations
public import Lean.Environment
public import Mathlib.Tactic.Linter.SuggestedName.Options

meta import Lean.Meta.Instances

/-!
# "Suggested name" linter

TODO
-/


open Lean Linter EnvLinter

public meta section

-- copied from `Mathlib.Lean.Name` because a linter prevents us from importing it here
private def Lean.Name.lastComponentAsString : Name → String
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => ""

/-- Decapitalise the given string according to the naming conventions. -/
def _root_.String.lowerStart (s : String) : String :=
  (manualException s).getD <|
    let n := largestNonLowerIndex s
    (s.positions.take n).fold (init := s) fun s ⟨⟨pos, _⟩, _⟩ ↦ (pos.set s (pos.get s).toLower)
where
  /-- If `s` is an exception to the rule, return its decapitalization instead. -/
  manualException (s : String) : Option String :=
    if
      -- Some excpetions to the rules:
      s.startsWith "Gamma"
      || s.startsWith "Lp"
      || s.startsWith "SL2"
      || (3 ≤ s.utf8ByteSize && String.Pos.Raw.get s ⟨0⟩ == 'I'
        && "ioc".contains (String.Pos.Raw.get s ⟨1⟩)
        && "ioc".contains (String.Pos.Raw.get s ⟨2⟩)
        && (s.utf8ByteSize = 3 || (String.Pos.Raw.get s ⟨4⟩).isUpper))
      || s matches "Ixx" | "Iotop"
    then
      some s
    else none

  /-- Return the number of characters that needs to be lowercased. -/
  largestNonLowerIndex (s : String) : Nat :=
    let start := s.takeWhile Char.isUpper
    let n := start.positions.length
    if start.endExclusive.get?.any Char.isLower then
      if n == 1 then
        1 -- e.g. `Real` ↦ `real`
      else
        n - 1 -- e.g. `NNReal` ↦ `nnReal`
    else
      if n == 1 then
        0 -- e.g. `X` ↦ `X` or `E6` ↦ `E6`
      else
        n -- e.g. `LE` ↦ `le` or  `LE'` ↦ `le'`

def Lean.Name.recommendedSpellings (env : Lean.Environment) (name : Lean.Name) : List String :=
  let recommended := Lean.Parser.Term.Doc.getRecommendedSpellingsForName env name
  if recommended.isEmpty then
    name.componentsRev.map toString |>.scanl (fun t c ↦ c ++ t.capitalize) "" |>.tail
  else
    recommended.map (·.recommendedSpelling) |>.toList.eraseDups

def List.getSingleton? {α : Type _} : List α → Option α
  | [a] => a
  | _ => none

def Lean.Name.suggestTheoremName (env : Lean.Environment) (name : Lean.Name) :
    CoreM (Option String) := do
  unless Lean.wasOriginallyTheorem env name do return none
  let .some decl := env.find? name | return none
  let consts ← decl.type.getUsedConstants
    |>.filter (not ∘ Lean.wasOriginallyTheorem env)
    |>.filterM (notM ∘ Lean.Meta.isInstance)
  let correctCasings :=
    consts.toList.flatMap (·.recommendedSpellings env) |>.map String.lowerStart |>.eraseDups
  let lowercaseToCorrectCasings := correctCasings.groupByKey String.toLower
  let lowercaseToCorrectCasing := lowercaseToCorrectCasings.filterMap fun _ ↦ List.getSingleton?
  let parts := name.lastComponentAsString.split '_'
  let newParts := parts.map fun s ↦ lowercaseToCorrectCasing.getD s.toString.toLower s.toString
  let newName := newParts.intercalateString "_"
  return if name.lastComponentAsString == newName then none else newName

@[builtin_env_linter linter.envLinter.suggestedName]
public def suggestedNameLinter : EnvLinter where
  test name := do
    let opts ← Linter.getLinterOptions
    unless Linter.getLinterValue linter.envLinter.suggestedName opts do return none

    let env ← getEnv
    if name.isInternalDetail then return none
    if (← Batteries.Tactic.Lint.isAutoDecl name) then return none
    if Linter.isDeprecated env name then return none
    let some suggestion ← name.suggestTheoremName env | return none
    return s!"→ {suggestion}"
  noErrorsFound := "All statement names are conform with the naming convention"
  errorsFound := "THE FOLLOWING STATEMENT NAMES ARE NOT FOLLOWING THE CONVENTION:"

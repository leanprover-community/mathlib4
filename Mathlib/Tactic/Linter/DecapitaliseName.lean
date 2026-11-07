/-
Copyright (c) 2026 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Snir Broshi, Jovan Gerbscheid
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header  -- shake: keep
meta import Lean.Parser.Term.Doc
meta import Std.Data.HashMap.AdditionalOperations
meta import Mathlib.Lean.Name
meta import Lean.Meta.Instances

/-! TODO -/

/-- Decapitalize the given string according to the naming conventions. -/
public meta def _root_.String.lowerStart (s : String) : String :=
  (manualException s).getD <|
    let positions := s.positions.take (largestNonLowerIndex s)
    positions.fold (init := s) fun s ⟨⟨pos, _⟩, _⟩ ↦ (pos.set s (pos.get s).toLower)
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

meta def Lean.Name.recommendedSpellings (env : Lean.Environment) (name : Lean.Name) : List String :=
  let recommended := Lean.Parser.Term.Doc.getRecommendedSpellingsForName env name
  if recommended.isEmpty then
    name.componentsRev.map toString |>.scanl (fun t c ↦ c ++ t.capitalize) "" |>.tail
  else
    recommended.map (·.recommendedSpelling) |>.toList.eraseDups

meta def List.getSingleton? {α : Type _} : List α → Option α
  | [a] => a
  | _ => none

meta def Lean.Name.suggestTheoremName (env : Lean.Environment) (name : Lean.Name) :
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

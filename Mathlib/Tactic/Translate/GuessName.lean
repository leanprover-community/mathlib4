/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster
-/
module

public meta import Std.Data.TreeMap.Basic
public meta import Mathlib.Data.String.Defs

/-!
# Name generation APIs for `to_additive`-like attributes
-/

public meta section

open Std

namespace Mathlib.Tactic.GuessName
open GuessName -- currently needed to enable projection notation

/-- The data that is required to guess the name of a translation. -/
structure GuessNameData where
  /--
  Dictionary used by `guessName` to autogenerate names.
  This only transforms single name components, unlike `abbreviationDict`.

  Note: `guessName` capitalizes the output according to the capitalization of the input.
  In order for this to work, the input should always start with a lower case letter, and the output
  should always start with an upper case letter.
  -/
  nameDict : Std.HashMap String (List String)
  /--
  We need to fix a few abbreviations after applying `nameDict`, i.e. replacing `ZeroLE` by `Nonneg`.
  This dictionary contains these fixes.
  The input should contain entries that is in `lowerCamelCase` (e.g. `ltzero`; the initial sequence
  of capital letters should be lower-cased) and the output should be in `UpperCamelCase`
  (e.g. `LTZero`).
  When applying the dictionary, we lower-case the output if the input was also given in lower-case.
  -/
  abbreviationDict : Std.HashMap String String

/-- A set of strings of names that end in a capital letter.
* If the string contains a lowercase letter, the string should be split between the first occurrence
  of a lower-case letter followed by an upper-case letter.
* If multiple strings have the same prefix, they should be grouped by prefix
* In this case, the second list should be prefix-free
  (no element can be a prefix of a later element)

Todo: automate the translation from `String` to an element in this `TreeMap`
  (but this would require having something similar to the `rb_lmap` from Lean 3). -/
def endCapitalNames : TreeMap String (List String) compare :=
  -- todo: we want something like
  -- endCapitalNamesOfList ["LE", "LT", "WF", "CoeTC", "CoeT", "CoeHTCT"]
  .ofList [("LE", [""]), ("LT", [""]), ("WF", [""]), ("Coe", ["TC", "T", "HTCT"])]

open String in
/-- This function takes a String and splits it into separate parts based on the following
[naming conventions](https://github.com/leanprover-community/mathlib4/wiki#naming-convention).

E.g. `#eval "InvHMulLEConjugate₂SMul_ne_top".splitCase` yields
`["Inv", "HMul", "LE", "Conjugate₂", "SMul", "_", "ne", "_", "top"]`. -/
partial def String.splitCase (s : String) (i₀ : Pos.Raw := 0) (r : List String := []) :
    List String := Id.run do
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := i₀.next s
  if i₁.atEnd s then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    return r.reverse
  /- We split the string in three cases
  * We split on both sides of `_` to keep them there when rejoining the string;
  * We split after a name in `endCapitalNames`;
  * We split after a lower-case letter that is followed by an upper-case letter
    (unless it is part of a name in `endCapitalNames`). -/
  if i₀.get s == '_' || i₁.get s == '_' then
    return splitCase (String.Pos.Raw.extract s i₁ s.rawEndPos) 0 <|
      (String.Pos.Raw.extract s 0 i₁)::r
  if (i₁.get s).isUpper then
    if let some strs := endCapitalNames[String.Pos.Raw.extract s 0 i₁]? then
      if let some (pref, newS) := strs.findSome?
        fun x : String ↦ (String.Pos.Raw.extract s i₁ s.rawEndPos).dropPrefix? x
          |>.map (x, ·.toString) then
        return splitCase newS 0 <| (String.Pos.Raw.extract s 0 i₁ ++ pref)::r
    if !(i₀.get s).isUpper then
      return splitCase (String.Pos.Raw.extract s i₁ s.rawEndPos) 0 <|
        (String.Pos.Raw.extract s 0 i₁)::r
  return splitCase s i₁ r

/-- Replaces characters in `s` by lower-casing the first characters until a non-upper-case character
is found. -/
partial def String.decapitalizeSeq (s : String) (i : String.Pos.Raw := 0) : String :=
  if i.atEnd s || !(i.get s).isUpper then
    s
  else
    decapitalizeSeq (i.set s (i.get s).toLower) <| i.next s

/-- If `r` starts with an upper-case letter, return `s`, otherwise return `s` with the
initial sequence of upper-case letters lower-cased. -/
def decapitalizeLike (r : String) (s : String) :=
  if String.Pos.Raw.get r 0 |>.isUpper then s else s.decapitalizeSeq

/-- Decapitalize the first element of a list if `s` starts with a lower-case letter.
Note that we need to decapitalize multiple characters in some cases,
in examples like `HMul` or `HAdd`. -/
def decapitalizeFirstLike (s : String) : List String → List String
  | x :: r => decapitalizeLike s x :: r
  | [] => []

/--
Apply the `nameDict` and decapitalize the output like the input.

E.g.
```
#eval applyNameDict ["Inv", "HMul", "LE", "Conjugate₂", "SMul", "_", "ne", "_", "top"]
```
yields `["Neg", "HAdd", "LE", "Conjugate₂", "VAdd", "_", "ne", "_", "top"]`.
-/
def applyNameDict (g : GuessNameData) : List String → List String
  | x :: s =>
    let z := match g.nameDict.get? x.toLower with
      | some y => decapitalizeFirstLike x y
      | none => [x]
    z ++ applyNameDict g s
  | [] => []

/-- Helper for `fixAbbreviation`.
Note: this function has a quadratic number of recursive calls, but is not a performance
bottleneck. -/
def fixAbbreviationAux (g : GuessNameData) : List String → List String → String
  | [], []     => ""
  | [], x::s   => x ++ fixAbbreviationAux g s []
  | pre::l, s' =>
    let s := s' ++ [pre]
    let t := String.join s
    /- If a name starts with upper-case, and contains an underscore, it cannot match anything in
    the abbreviation dictionary. This is necessary to correctly translate something like
    `fixAbbreviation ["eventually", "LE", "_", "one"]` to `"eventuallyLE_one"`, since otherwise the
    substring `LE_zero` gets replaced by `Nonpos`. -/
    if pre == "_" && (String.Pos.Raw.get t 0).isUpper then
      s[0]! ++ fixAbbreviationAux g (s.drop 1 ++ l) []
    else match g.abbreviationDict.get? t.decapitalizeSeq with
    | some post => decapitalizeLike t post ++ fixAbbreviationAux g l []
    | none      => fixAbbreviationAux g l s
  termination_by l s => (l.length + s.length, l.length)
  decreasing_by all_goals grind

/-- Replace substrings according to `abbreviationDict`, matching the case of the first letter.

Example:
```
#eval applyNameDict ["Mul", "Support"]
```
gives the preliminary translation `["Add", "Support"]`. Subsequently
```
#eval fixAbbreviation ["Add", "Support"]
```
"fixes" this translation and returns `Support`.
-/
def fixAbbreviation (g : GuessNameData) (l : List String) : String :=
  fixAbbreviationAux g l []

/--
Autogenerate additive name.
This runs in several steps:
1) Split according to capitalisation rule and at `_`.
2) Apply word-by-word translation rules.
3) Fix up abbreviations that are not word-by-word translations, like "addComm" or "Nonneg".
-/
def guessName (g : GuessNameData) : String → String :=
  String.mapTokens '\'' <|
  fun s =>
    fixAbbreviation g <|
    applyNameDict g <|
    s.splitCase

end Mathlib.Tactic.GuessName

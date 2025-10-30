/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster
-/

import Std.Data.TreeMap.Basic
import Mathlib.Data.String.Defs

/-!
# Name generation APIs for `to_additive`
-/

open Std

namespace ToAdditive
open ToAdditive

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
partial def String.splitCase (s : String) (i₀ : Pos := 0) (r : List String := []) :
    List String := Id.run do
  -- We test if we need to split between `i₀` and `i₁`.
  let i₁ := s.next i₀
  if s.atEnd i₁ then
    -- If `i₀` is the last position, return the list.
    let r := s::r
    return r.reverse
  /- We split the string in three cases
  * We split on both sides of `_` to keep them there when rejoining the string;
  * We split after a name in `endCapitalNames`;
  * We split after a lower-case letter that is followed by an upper-case letter
    (unless it is part of a name in `endCapitalNames`). -/
  if s.get i₀ == '_' || s.get i₁ == '_' then
    return splitCase (s.extract i₁ s.endPos) 0 <| (s.extract 0 i₁)::r
  if (s.get i₁).isUpper then
    if let some strs := endCapitalNames[s.extract 0 i₁]? then
      if let some (pref, newS) := strs.findSome?
        fun x : String ↦ (s.extract i₁ s.endPos).dropPrefix? x |>.map (x, ·.toString) then
        return splitCase newS 0 <| (s.extract 0 i₁ ++ pref)::r
    if !(s.get i₀).isUpper then
      return splitCase (s.extract i₁ s.endPos) 0 <| (s.extract 0 i₁)::r
  return splitCase s i₁ r

/-- Replaces characters in `s` by lower-casing the first characters until a non-upper-case character
is found. -/
partial def String.decapitalizeSeq (s : String) (i : String.Pos := 0) : String :=
  if s.atEnd i || !(s.get i).isUpper then
    s
  else
    decapitalizeSeq (s.set i (s.get i).toLower) <| s.next i


/-- If `r` starts with an upper-case letter, return `s`, otherwise return `s` with the
initial sequence of upper-case letters lower-cased. -/
def decapitalizeLike (r : String) (s : String) :=
  if r.get 0 |>.isUpper then s else s.decapitalizeSeq

/-- Decapitalize the first element of a list if `s` starts with a lower-case letter.
Note that we need to decapitalize multiple characters in some cases,
in examples like `HMul` or `HAdd`. -/
def decapitalizeFirstLike (s : String) : List String → List String
  | x :: r => decapitalizeLike s x :: r
  | [] => []

/--
Dictionary used by `guessName` to autogenerate names.
This only transforms single name components, unlike `abbreviationDict`.

Note: `guessName` capitalizes the output according to the capitalization of the input.
In order for this to work, the input should always be lower case, and the output always upper case.
-/
def nameDict : Std.HashMap String (List String) :=
  .ofList [("one", ["Zero"]),
    ("mul", ["Add"]),
    ("smul", ["VAdd"]),
    ("inv", ["Neg"]),
    ("div", ["Sub"]),
    ("prod", ["Sum"]),
    ("hmul", ["HAdd"]),
    ("hsmul", ["HVAdd"]),
    ("hdiv", ["HSub"]),
    ("hpow", ["HSMul"]),
    ("finprod", ["Finsum"]),
    ("tprod", ["TSum"]),
    ("pow", ["NSMul"]),
    ("npow", ["NSMul"]),
    ("zpow", ["ZSMul"]),
    ("mabs", ["Abs"]),
    ("monoid", ["Add", "Monoid"]),
    ("submonoid", ["Add", "Submonoid"]),
    ("group", ["Add", "Group"]),
    ("subgroup", ["Add", "Subgroup"]),
    ("semigroup", ["Add", "Semigroup"]),
    ("magma", ["Add", "Magma"]),
    ("haar", ["Add", "Haar"]),
    ("prehaar", ["Add", "Prehaar"]),
    ("unit", ["Add", "Unit"]),
    ("units", ["Add", "Units"]),
    ("cyclic", ["Add", "Cyclic"]),
    ("semigrp", ["Add", "Semigrp"]),
    ("grp", ["Add", "Grp"]),
    ("commute", ["Add", "Commute"]),
    ("semiconj", ["Add", "Semiconj"]),
    ("rootable", ["Divisible"]),
    ("zpowers", ["ZMultiples"]),
    ("powers", ["Multiples"]),
    ("multipliable", ["Summable"]),
    ("gpfree", ["APFree"]),
    ("quantale", ["Add", "Quantale"]),
    ("square", ["Even"]),
    ("mconv", ["Conv"]),
    ("irreducible", ["Add", "Irreducible"]),
    ("mlconvolution", ["LConvolution"])]

/--
Apply the `nameDict` and decapitalize the output like the input.
-/
def applyNameDict : List String → List String
  | x :: s =>
    let y := nameDict.get? x.toLower
    let z := match y with
      | some y' => decapitalizeFirstLike x y'
      | none => [x]
    z ++ applyNameDict s
  | [] => []

/--
We need to fix a few abbreviations after applying `nameDict`, i.e. replacing `ZeroLE` by `Nonneg`.
This dictionary contains these fixes.
The input should contain entries that is in `lowerCamelCase` (e.g. `ltzero`; the initial sequence
of capital letters should be lower-cased) and the output should be in `UpperCamelCase`
(e.g. `LTZero`).
When applying the dictionary, we lower-case the output if the input was also given in lower-case.
-/
def abbreviationDict : Std.HashMap String String :=
  .ofList [("isCancelAdd", "IsCancelAdd"),
    ("isLeftCancelAdd", "IsLeftCancelAdd"),
    ("isRightCancelAdd", "IsRightCancelAdd"),
    ("cancelAdd", "AddCancel"),
    ("leftCancelAdd", "AddLeftCancel"),
    ("rightCancelAdd", "AddRightCancel"),
    ("cancelCommAdd", "AddCancelComm"),
    ("commAdd", "AddComm"),
    ("zero_le", "Nonneg"),
    ("zeroLE", "Nonneg"),
    ("zero_lt", "Pos"),
    ("zeroLT", "Pos"),
    ("lezero", "Nonpos"),
    ("le_zero", "Nonpos"),
    ("ltzero", "Neg"),
    ("lt_zero", "Neg"),
    ("addSingle", "Single"),
    ("add_single", "Single"),
    ("addSupport", "Support"),
    ("add_support", "Support"),
    ("addTSupport", "TSupport"),
    ("add_tsupport", "TSupport"),
    ("addIndicator", "Indicator"),
    ("add_indicator", "Indicator"),
    ("isEven", "Even"),
    -- "Regular" is well-used in mathlib with various meanings (e.g. in
    -- measure theory) and a direct translation
    -- "regular" --> "addRegular" in `nameDict` above seems error-prone.
    ("isRegular", "IsAddRegular"),
    ("isLeftRegular", "IsAddLeftRegular"),
    ("isRightRegular", "IsAddRightRegular"),
    ("hasFundamentalDomain", "HasAddFundamentalDomain"),
    ("quotientMeasure", "AddQuotientMeasure"),
    ("negFun", "InvFun"),
    ("uniqueProds", "UniqueSums"),
    ("orderOf", "AddOrderOf"),
    ("zeroLePart", "PosPart"),
    ("leZeroPart", "NegPart"),
    ("isScalarTower", "VAddAssocClass"),
    ("isOfFinOrder", "IsOfFinAddOrder"),
    ("isCentralScalar", "IsCentralVAdd"),
    ("function_addSemiconj", "Function_semiconj"),
    ("function_addCommute", "Function_commute"),
    ("divisionAddMonoid", "SubtractionMonoid"),
    ("subNegZeroAddMonoid", "SubNegZeroMonoid"),
    ("modularCharacter", "AddModularCharacter")]

/-- Helper for `fixAbbreviation`.
Note: this function has a quadratic number of recursive calls, but is not a performance
bottleneck. -/
def fixAbbreviationAux : List String → List String → String
  | [], []     => ""
  | [], x::s   => x ++ fixAbbreviationAux s []
  | pre::l, s' =>
    let s := s' ++ [pre]
    let t := String.join s
    /- If a name starts with upper-case, and contains an underscore, it cannot match anything in
    the abbreviation dictionary. This is necessary to correctly translate something like
    `fixAbbreviation ["eventually", "LE", "_", "one"]`, since otherwise the substring `LE_zero` gets
    replaced by `Nonpos`. -/
    if pre == "_" && (t.get 0).isUpper then
      s[0]! ++ fixAbbreviationAux (s.drop 1 ++ l) []
    else match abbreviationDict.get? t.decapitalizeSeq with
    | some post => decapitalizeLike t post ++ fixAbbreviationAux l []
    | none      => fixAbbreviationAux l s
  termination_by l s => (l.length + s.length, l.length)
  decreasing_by all_goals grind

/-- Replace substrings according to `abbreviationDict`, matching the case of the first letter. -/
def fixAbbreviation (l : List String) : String :=
  fixAbbreviationAux l []

/--
Autogenerate additive name.
This runs in several steps:
1) Split according to capitalisation rule and at `_`.
2) Apply word-by-word translation rules.
3) Fix up abbreviations that are not word-by-word translations, like "addComm" or "Nonneg".
-/
def guessName : String → String :=
  String.mapTokens '\'' <|
  fun s =>
    fixAbbreviation <|
    applyNameDict <|
    s.splitCase

end ToAdditive

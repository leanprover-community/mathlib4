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
partial def _root_.String.splitCase (s : String) (i₀ : Pos := 0) (r : List String := []) :
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

/-- Helper for `capitalizeLike`. -/
partial def capitalizeLikeAux (s : String) (i : String.Pos := 0) (p : String) : String :=
  if p.atEnd i || s.atEnd i then
    p
  else
    let j := p.next i
    if (s.get i).isLower then
      capitalizeLikeAux s j <| p.set i (p.get i |>.toLower)
    else if (s.get i).isUpper then
      capitalizeLikeAux s j <| p.set i (p.get i |>.toUpper)
    else
      capitalizeLikeAux s j p

/-- Capitalizes `s` char-by-char like `r`. If `s` is longer, it leaves the tail untouched. -/
def capitalizeLike (r : String) (s : String) :=
  capitalizeLikeAux r 0 s

/-- Capitalize First element of a list like `s`.
Note that we need to capitalize multiple characters in some cases,
in examples like `HMul` or `hAdd`. -/
def capitalizeFirstLike (s : String) : List String → List String
  | x :: r => capitalizeLike s x :: r
  | [] => []

/--
Dictionary used by `guessName` to autogenerate names.

Note: `guessName` capitalizes first element of the output according to
capitalization of the input. Input and first element should therefore be lower-case,
2nd element should be capitalized properly.
-/
def nameDict : String → List String
  | "one"           => ["zero"]
  | "mul"           => ["add"]
  | "smul"          => ["vadd"]
  | "inv"           => ["neg"]
  | "div"           => ["sub"]
  | "prod"          => ["sum"]
  | "hmul"          => ["hadd"]
  | "hsmul"         => ["hvadd"]
  | "hdiv"          => ["hsub"]
  | "hpow"          => ["hsmul"]
  | "finprod"       => ["finsum"]
  | "tprod"         => ["tsum"]
  | "pow"           => ["nsmul"]
  | "npow"          => ["nsmul"]
  | "zpow"          => ["zsmul"]
  | "mabs"          => ["abs"]
  | "monoid"        => ["add", "Monoid"]
  | "submonoid"     => ["add", "Submonoid"]
  | "group"         => ["add", "Group"]
  | "subgroup"      => ["add", "Subgroup"]
  | "semigroup"     => ["add", "Semigroup"]
  | "magma"         => ["add", "Magma"]
  | "haar"          => ["add", "Haar"]
  | "prehaar"       => ["add", "Prehaar"]
  | "unit"          => ["add", "Unit"]
  | "units"         => ["add", "Units"]
  | "cyclic"        => ["add", "Cyclic"]
  | "rootable"      => ["divisible"]
  | "semigrp"       => ["add", "Semigrp"]
  | "grp"           => ["add", "Grp"]
  | "commute"       => ["add", "Commute"]
  | "semiconj"      => ["add", "Semiconj"]
  | "zpowers"       => ["zmultiples"]
  | "powers"        => ["multiples"]
  | "multipliable"  => ["summable"]
  | "gpfree"        => ["apfree"]
  | "quantale"      => ["add", "Quantale"]
  | "square"        => ["even"]
  | "mconv"         => ["conv"]
  | "irreducible"   => ["add", "Irreducible"]
  | "mlconvolution" => ["lconvolution"]
  | x               => [x]

/--
Turn each element to lower-case, apply the `nameDict` and
capitalize the output like the input.
-/
def applyNameDict : List String → List String
  | x :: s => (capitalizeFirstLike x (nameDict x.toLower)) ++ applyNameDict s
  | [] => []


/--
The capitalization heuristic of `applyNameDict` doesn't work in the following cases,
here we fix them.
-/
def fixCapitalization : List String → List String
  --
  | "HSmul" :: s                      => "HSMul" :: fixCapitalization s -- from `HPow`
  | "NSmul" :: s                      => "NSMul" :: fixCapitalization s -- from `NPow`
  | "Nsmul" :: s                      => "NSMul" :: fixCapitalization s -- from `Pow`
  | "ZSmul" :: s                      => "ZSMul" :: fixCapitalization s -- from `ZPow`
  | x :: s                            => x :: fixCapitalization s
  | []                                => []

/--
We need to fix a few abbreviations after applying `nameDict`, i.e. replacing `ZeroLE` by `Nonneg`.
This dictionary contains these fixes. The dictionary should only contain entries that start with
a lower-case letter in both the input and the output.
When applying the dictionary, we match case of the output with the case of the input
*in the first character only*. In most cases this is sufficient. For example, the entry
`"orderOf" => "addOrderOf"` will also map `OrderOf` to `AddOrderOf`.
If the input or output have capital letters after the first character, they must be left
capitalized, resulting e.g. in `"lEZero" => "nonpos"`.
-/
def abbreviationDict : String → Option String
  | "isCancelAdd"      => "isCancelAdd"
  | "isLeftCancelAdd"  => "isLeftCancelAdd"
  | "isRightCancelAdd" => "isRightCancelAdd"
  | "cancelAdd"        => "addCancel"
  | "leftCancelAdd"    => "addLeftCancel"
  | "rightCancelAdd"   => "addRightCancel"
  | "cancelCommAdd"    => "addCancelComm"
  | "commAdd"          => "addComm"
  | "zero_le"          => "nonneg"
  | "zeroLE"           => "nonneg"
  | "zero_lt"          => "pos"
  | "zeroLT"           => "pos"
  | "lEZero"           => "nonpos"
  | "le_zero"          => "nonpos"
  | "lTZero"           => "neg"
  | "lt_zero"          => "neg"
  | "addSingle"        => "single"
  | "add_single"       => "single"
  | "addSupport"       => "support"
  | "add_support"      => "support"
  | "addTSupport"      => "tsupport"
  | "add_tsupport"     => "tsupport"
  | "addIndicator"     => "indicator"
  | "add_indicator"    => "indicator"
  | "isEven"           => "even"
  -- "Regular" is well-used in mathlib with various meanings (e.g. in
  -- measure theory) and a direct translation
  -- "regular" --> "addRegular" in `nameDict` above seems error-prone.
  | "isRegular"        => "isAddRegular"
  | "isLeftRegular"    => "isAddLeftRegular"
  | "isRightRegular"   => "isAddRightRegular"
  | "hasFundamentalDomain" => "hasAddFundamentalDomain"
  | "quotientMeasure"  => "addQuotientMeasure"
  | "negFun"           => "invFun"
  | "uniqueProds"      => "uniqueSums"
  | "orderOf"          => "addOrderOf"
  | "zeroLePart"       => "posPart"
  | "lEZeroPart"       => "negPart"
  | "leZeroPart"       => "negPart"
  | "isScalarTower"    => "vaddAssocClass"
  | "isOfFinOrder"     => "isOfFinAddOrder"
  | "isCentralScalar"  => "isCentralVAdd"
  | "function_addSemiconj" => "function_semiconj"
  | "function_addCommute"  => "function_commute"
  | "divisionAddMonoid"    => "subtractionMonoid"
  | "subNegZeroAddMonoid"  => "subNegZeroMonoid"
  | "modularCharacter" => "addModularCharacter"
  | _                  => none

/-- Helper for `fixAbbreviation`. -/
partial def fixAbbreviationAux : List String → List String → String
  | [], []     => ""
  | [], x::s   => x ++ fixAbbreviationAux s []
  | pre::l, s' =>
    let s := s' ++ [pre]
    match abbreviationDict <| String.join s |>.decapitalize with
    | some post => capitalizeLike (s[0]!.take 1) post ++ fixAbbreviationAux l []
    | none      =>
      -- have : WellFoundedRelation.rel (l.length + s.length, l.length)
      --  ((pre::l).length + s'.length, (pre::l).length) := by
      --   sorry
      fixAbbreviationAux l s
  -- termination_by l s => (l.length + s.length, l.length) -- doesn't work?


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
    fixCapitalization <|
    applyNameDict <|
    s.splitCase

end ToAdditive

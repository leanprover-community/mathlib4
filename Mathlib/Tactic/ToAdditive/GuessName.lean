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
partial def _root_.String.splitCase (s : String) (i₀ : Pos.Raw := 0) (r : List String := []) :
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

/-- Helper for `capitalizeLike`. -/
partial def capitalizeLikeAux (s : String) (i : String.Pos.Raw := 0) (p : String) : String :=
  if i.atEnd p || i.atEnd s then
    p
  else
    let j := i.next p
    if (i.get s).isLower then
      capitalizeLikeAux s j <| i.set p (i.get p |>.toLower)
    else if (i.get s).isUpper then
      capitalizeLikeAux s j <| i.set p (i.get p |>.toUpper)
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
There are a few abbreviations we use. For example "Nonneg" instead of "ZeroLE"
or "addComm" instead of "commAdd".
Note: The input to this function is case sensitive!
Todo: A lot of abbreviations here are manual fixes and there might be room to
improve the naming logic to reduce the size of `fixAbbreviation`.
-/
def fixAbbreviation : List String → List String
  | "is" :: "Cancel" :: "Add" :: s    => "isCancelAdd" :: fixAbbreviation s
  | "Is" :: "Cancel" :: "Add" :: s    => "IsCancelAdd" :: fixAbbreviation s
  | "is" :: "Left" :: "Cancel" :: "Add" :: s  => "isLeftCancelAdd" :: fixAbbreviation s
  | "Is" :: "Left" :: "Cancel" :: "Add" :: s  => "IsLeftCancelAdd" :: fixAbbreviation s
  | "is" :: "Right" :: "Cancel" :: "Add" :: s => "isRightCancelAdd" :: fixAbbreviation s
  | "Is" :: "Right" :: "Cancel" :: "Add" :: s => "IsRightCancelAdd" :: fixAbbreviation s
  | "cancel" :: "Add" :: s            => "addCancel" :: fixAbbreviation s
  | "Cancel" :: "Add" :: s            => "AddCancel" :: fixAbbreviation s
  | "left" :: "Cancel" :: "Add" :: s  => "addLeftCancel" :: fixAbbreviation s
  | "Left" :: "Cancel" :: "Add" :: s  => "AddLeftCancel" :: fixAbbreviation s
  | "right" :: "Cancel" :: "Add" :: s => "addRightCancel" :: fixAbbreviation s
  | "Right" :: "Cancel" :: "Add" :: s => "AddRightCancel" :: fixAbbreviation s
  | "cancel" :: "Comm" :: "Add" :: s  => "addCancelComm" :: fixAbbreviation s
  | "Cancel" :: "Comm" :: "Add" :: s  => "AddCancelComm" :: fixAbbreviation s
  | "comm" :: "Add" :: s              => "addComm" :: fixAbbreviation s
  | "Comm" :: "Add" :: s              => "AddComm" :: fixAbbreviation s
  | "Zero" :: "LE" :: s               => "Nonneg" :: fixAbbreviation s
  | "zero" :: "_" :: "le" :: s        => "nonneg" :: fixAbbreviation s
  | "zero" :: "LE" :: s               => "nonneg" :: fixAbbreviation s
  | "Zero" :: "LT" :: s               => "Pos" :: fixAbbreviation s
  | "zero" :: "_" :: "lt" :: s        => "pos" :: fixAbbreviation s
  | "zero" :: "LT" :: s               => "pos" :: fixAbbreviation s
  | "LE" :: "Zero" :: s               => "Nonpos" :: fixAbbreviation s
  | "le" :: "_" :: "zero" :: s        => "nonpos" :: fixAbbreviation s
  | "LT" :: "Zero" :: s               => "Neg" :: fixAbbreviation s
  | "lt" :: "_" :: "zero" :: s        => "neg" :: fixAbbreviation s
  | "Add" :: "Single" :: s            => "Single" :: fixAbbreviation s
  | "add" :: "Single" :: s            => "single" :: fixAbbreviation s
  | "add" :: "_" :: "single" :: s     => "single" :: fixAbbreviation s
  | "Add" :: "Support" :: s           => "Support" :: fixAbbreviation s
  | "add" :: "Support" :: s           => "support" :: fixAbbreviation s
  | "add" :: "_" :: "support" :: s    => "support" :: fixAbbreviation s
  | "Add" :: "TSupport" :: s          => "TSupport" :: fixAbbreviation s
  | "add" :: "TSupport" :: s          => "tsupport" :: fixAbbreviation s
  | "add" :: "_" :: "tsupport" :: s   => "tsupport" :: fixAbbreviation s
  | "Add" :: "Indicator" :: s         => "Indicator" :: fixAbbreviation s
  | "add" :: "Indicator" :: s         => "indicator" :: fixAbbreviation s
  | "add" :: "_" :: "indicator" :: s  => "indicator" :: fixAbbreviation s
  | "is" :: "Even" :: s             => "even" :: fixAbbreviation s
  | "Is" :: "Even" :: s             => "Even" :: fixAbbreviation s
  -- "Regular" is well-used in mathlib with various meanings (e.g. in
  -- measure theory) and a direct translation
  -- "regular" --> ["add", "Regular"] in `nameDict` above seems error-prone.
  | "is" :: "Regular" :: s            => "isAddRegular" :: fixAbbreviation s
  | "Is" :: "Regular" :: s            => "IsAddRegular" :: fixAbbreviation s
  | "is" :: "Left" :: "Regular" :: s  => "isAddLeftRegular" :: fixAbbreviation s
  | "Is" :: "Left" :: "Regular" :: s  => "IsAddLeftRegular" :: fixAbbreviation s
  | "is" :: "Right" :: "Regular" :: s => "isAddRightRegular" :: fixAbbreviation s
  | "Is" :: "Right" :: "Regular" :: s => "IsAddRightRegular" :: fixAbbreviation s
  | "Has" :: "Fundamental" :: "Domain" :: s => "HasAddFundamentalDomain" :: fixAbbreviation s
  | "has" :: "Fundamental" :: "Domain" :: s => "hasAddFundamentalDomain" :: fixAbbreviation s
  | "Quotient" :: "Measure" :: s => "AddQuotientMeasure" :: fixAbbreviation s
  | "quotient" :: "Measure" :: s => "addQuotientMeasure" :: fixAbbreviation s
  -- the capitalization heuristic of `applyNameDict` doesn't work in the following cases
  | "HSmul" :: s                      => "HSMul" :: fixAbbreviation s -- from `HPow`
  | "NSmul" :: s                      => "NSMul" :: fixAbbreviation s -- from `NPow`
  | "Nsmul" :: s                      => "NSMul" :: fixAbbreviation s -- from `Pow`
  | "ZSmul" :: s                      => "ZSMul" :: fixAbbreviation s -- from `ZPow`
  | "neg" :: "Fun" :: s               => "invFun" :: fixAbbreviation s
  | "Neg" :: "Fun" :: s               => "InvFun" :: fixAbbreviation s
  | "unique" :: "Prods" :: s          => "uniqueSums" :: fixAbbreviation s
  | "Unique" :: "Prods" :: s          => "UniqueSums" :: fixAbbreviation s
  | "order" :: "Of" :: s              => "addOrderOf" :: fixAbbreviation s
  | "Order" :: "Of" :: s              => "AddOrderOf" :: fixAbbreviation s
  | "is"::"Of"::"Fin"::"Order"::s     => "isOfFinAddOrder" :: fixAbbreviation s
  | "Is"::"Of"::"Fin"::"Order"::s     => "IsOfFinAddOrder" :: fixAbbreviation s
  | "is" :: "Central" :: "Scalar" :: s  => "isCentralVAdd" :: fixAbbreviation s
  | "Is" :: "Central" :: "Scalar" :: s  => "IsCentralVAdd" :: fixAbbreviation s
  | "is" :: "Scalar" :: "Tower" :: s  => "vaddAssocClass" :: fixAbbreviation s
  | "Is" :: "Scalar" :: "Tower" :: s  => "VAddAssocClass" :: fixAbbreviation s
  | "function" :: "_" :: "add" :: "Semiconj" :: s
                                      => "function" :: "_" :: "semiconj" :: fixAbbreviation s
  | "function" :: "_" :: "add" :: "Commute" :: s
                                      => "function" :: "_" :: "commute" :: fixAbbreviation s
  | "Zero" :: "Le" :: "Part" :: s         => "PosPart" :: fixAbbreviation s
  | "Le" :: "Zero" :: "Part" :: s         => "NegPart" :: fixAbbreviation s
  | "zero" :: "Le" :: "Part" :: s         => "posPart" :: fixAbbreviation s
  | "le" :: "Zero" :: "Part" :: s         => "negPart" :: fixAbbreviation s
  | "Division" :: "Add" :: "Monoid" :: s => "SubtractionMonoid" :: fixAbbreviation s
  | "division" :: "Add" :: "Monoid" :: s => "subtractionMonoid" :: fixAbbreviation s
  | "Sub" :: "Neg" :: "Zero" :: "Add" :: "Monoid" :: s => "SubNegZeroMonoid" :: fixAbbreviation s
  | "sub" :: "Neg" :: "Zero" :: "Add" :: "Monoid" :: s => "subNegZeroMonoid" :: fixAbbreviation s
  | "modular" :: "Character" :: s => "addModularCharacter" :: fixAbbreviation s
  | "Modular" :: "Character" :: s => "AddModularCharacter" :: fixAbbreviation s
  | x :: s                            => x :: fixAbbreviation s
  | []                                => []

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
    String.join <|
    fixAbbreviation <|
    applyNameDict <|
    s.splitCase

end ToAdditive

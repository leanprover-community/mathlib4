/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Keeley Hoek, Floris van Doorn, Chris Bailey
-/
import Batteries.Data.List.Basic
import Mathlib.Mathport.Rename

#align_import data.string.defs from "leanprover-community/mathlib"@"e7131068d9696deec51e6cd7668b6d9ac69af6a4"

/-!
# Definitions for `String`

This file defines a bunch of functions for the `String` datatype.
-/

namespace String

#align string.split_on String.splitOn
#align string.is_prefix_of String.isPrefixOf
#align string.starts_with String.startsWith
#align string.ends_with String.endsWith
#align string.is_nat String.isNat

/-- Pad `s : String` with repeated occurrences of `c : Char` until it's of length `n`.
  If `s` is initially larger than `n`, just return `s`. -/
def leftpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  ⟨List.leftpad n c s.data⟩

/-- Construct the string consisting of `n` copies of the character `c`. -/
def replicate (n : Nat) (c : Char) : String :=
  ⟨List.replicate n c⟩

-- TODO bring this definition in line with the above, either by:
-- adding `List.rightpad` to Batteries and changing the definition of `rightpad` here to match
-- or by changing the definition of `leftpad` above to match this
/-- Pad `s : String` with repeated occurrences of `c : Char` on the right until it's of length `n`.
  If `s` is initially larger than `n`, just return `s`. -/
def rightpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  s ++ String.replicate (n - s.length) c

/-- `s.IsPrefix t` checks if the string `s` is a prefix of the string `t`. -/
def IsPrefix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.IsPrefix d1 d2

/-- `s.IsSuffix t` checks if the string `s` is a suffix of the string `t`. -/
def IsSuffix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.IsSuffix d1 d2

/-- `String.mapTokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def mapTokens (c : Char) (f : String → String) : String → String :=
  intercalate (singleton c) ∘ List.map f ∘ (·.split (· = c))
#align string.map_tokens String.mapTokens

/-- `getRest s t` returns `some r` if `s = t ++ r`.
If `t` is not a prefix of `s`, it returns `none`. -/
def getRest (s t : String) : Option String :=
  List.asString <$> s.toList.getRest t.toList
#align string.get_rest String.getRest

#align string.popn String.drop

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise `'A'`. -/
def head (s : String) : Char :=
  s.iter.curr
#align string.head String.head

end String

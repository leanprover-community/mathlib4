/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Keeley Hoek, Floris van Doorn, Chris Bailey

! This file was ported from Lean 3 source module data.string.defs
! leanprover-community/mathlib commit e7131068d9696deec51e6cd7668b6d9ac69af6a4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Std.Data.List.Basic
import Mathlib.Mathport.Rename

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
def leftpad (n : Nat) (c : Char) (s : String) : String :=
  ⟨List.leftpad n c s.data⟩

/-- Construct the string consisting of `n` copies of the character `c`. -/
def replicate (n : Nat) (c : Char) : String :=
  ⟨List.replicate n c⟩

/-- `s.isPrefix t` checks if the string `s` is a prefix of the string `t`. -/
def isPrefix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.isPrefix d1 d2

/-- `s.isSuffix t` checks if the string `s` is a suffix of the string `t`. -/
def isSuffix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.isSuffix d1 d2

/-- `String.mapTokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def mapTokens (c : Char) (f : String → String) : String → String :=
  intercalate (singleton c) ∘ List.map f ∘ (·.split (· = c))
#align string.map_tokens String.mapTokens

/-- `isPrefixOf? pre s` returns `some post` if `s = pre ++ post`.
If `pre` is not a prefix of `s`, it returns `none`. -/
def isPrefixOf? (pre s : String) : Option String :=
  if startsWith s pre then some <| s.drop pre.length else none

/-- Return true iff `p` is a suffix of `s`. -/
def isSuffixOf (p s : String) : Bool :=
  substrEq p 0 s (s.endPos - p.endPos) p.endPos.byteIdx
#align string.is_suffix_of String.isSuffixOf

/-- `isSuffixOf? suff s` returns `some pre` if `s = pre ++ suff`.
If `suff` is not a suffix of `s`, it returns `none`. -/
def isSuffixOf? (suff s : String) : Option String :=
  if s.endsWith suff then some <| s.dropRight suff.length else none

/-- `s.stripPrefix p` will remove `p` from the beginning of `s` if it occurs there,
or otherwise return `s`. -/
def stripPrefix (s p : String) :=
  if s.startsWith p then s.drop p.length else s

/-- `s.stripSuffix p` will remove `p` from the end of `s` if it occurs there,
or otherwise return `s`. -/
def stripSuffix (s p : String) :=
  if s.endsWith p then s.dropRight p.length else s

/-- Count the occurrences of a character in a string. -/
def count (s : String) (c : Char) : Nat :=
  s.foldl (fun n d => if d = c then n + 1 else n) 0

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

/-
Copyright (c) 2021 Chris Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Bailey
-/
import Std.Data.List.Basic

namespace String

/-- pad `s : String` with repeated occurrences of `c : Char` until it's of length `n`.
  If `s` is initially larger than `n`, just return `s`. -/
def leftpad (n : Nat) (c : Char) (s : String) : String :=
⟨List.leftpad n c s.data⟩

/-- Construct the string consisting of `n` copies of the character `c`. -/
def replicate (n : Nat) (c : Char) : String := ⟨List.replicate n c⟩

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

/-- `isPrefixOf? pre s` returns `some post` if `s = pre ++ post`.
  If `pre` is not a prefix of `s`, it returns `none`. -/
def isPrefixOf? (pre s : String) : Option String :=
  if startsWith s pre then some <| s.drop pre.length else none

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

end String

import Std.Data.List.Basic

namespace String

/-- pad `s : String` with repeated occurrences of `c : Char` until it's of length `n`.
  If `s` is initially larger than `n`, just return `s`. -/
def leftpad (n : Nat) (c : Char) (s : String) : String :=
⟨List.leftpad n c s.data⟩

def replicate (n : Nat) (c : Char) : String := ⟨List.replicate n c⟩

def isPrefix : String → String → Prop
| ⟨d1⟩, ⟨d2⟩ => List.isPrefix d1 d2

def isSuffix : String → String → Prop
| ⟨d1⟩, ⟨d2⟩ => List.isSuffix d1 d2

/-- `string.mapTokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def mapTokens (c : Char) (f : String → String) : String → String :=
intercalate (singleton c) ∘ List.map f ∘ (·.split (· = c))

/-- `isPrefixOf? pre s` returns `some post` if `s = pre ++ post`.
  If `pre` is not a prefix of `s`, it returns `none`. -/
def isPrefixOf? (pre s : String) : Option String :=
  if startsWith s pre then some <| s.drop pre.length else none

/-- Removes the first `n` elements from the string `s` -/
def popn (s : String) (n : Nat) : String :=
  ⟨s.toList.drop n⟩

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : String) : Char :=
  s.iter.curr

end String

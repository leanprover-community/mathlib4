import Std.Data.List.Basic
import Mathlib.Mathport.Rename

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

/-- `String.mapTokens c f s` tokenizes `s : String` on `c : Char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def mapTokens (c : Char) (f : String → String) : String → String :=
intercalate (singleton c) ∘ List.map f ∘ (·.split (· = c))

/-- `getRest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none`. -/
def getRest (s t : String) : Option String :=
  List.asString <$> s.toList.getRest t.toList
#align string.get_rest String.getRest

/-- Removes the first `n` elements from the string `s`. -/
def popn (s : String) (n : Nat) : String :=
  (s.mkIterator.nextn n).remainingToString
#align string.popn String.popn

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : String) : Char :=
  s.mkIterator.curr
#align string.head String.head

end String

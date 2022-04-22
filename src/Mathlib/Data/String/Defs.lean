import Mathlib.Data.List.Basic

namespace String

/-- pad `s : String` with repeated occurrences of `c : Char` until it's of length `n`.
  If `s` is initially larger than `n`, just return `s`. -/
def leftpad (n : Nat) (c : Char) (s : String) : String :=
⟨List.leftpad n c s.data⟩

def repeat (c : Char) (n : Nat) : String := ⟨List.repeat c n⟩

def isPrefix : String -> String -> Prop
| ⟨d1⟩, ⟨d2⟩ => List.isPrefix d1 d2

def isSuffix : String -> String -> Prop
| ⟨d1⟩, ⟨d2⟩ => List.isSuffix d1 d2

/-- `string.mapTokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def mapTokens (c : Char) (f : String → String) : String → String :=
intercalate (singleton c) ∘ List.map f ∘ (·.split (· = c))

end String

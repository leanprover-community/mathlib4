import Init.Data.String

/-!
These are a few functions concerning `String` that should be upstreamed to Lean itself.
-/

open Lean

namespace String

def findAllAux (s : String) (p : Char → Bool) (stopPos : Pos) (pos : Pos) (acc : Array Pos := #[]) :
    Array Pos :=
  if h : pos < stopPos then
    have := Nat.sub_lt_sub_left h (lt_next s pos)
    if p (s.get pos) then
      findAllAux s p stopPos (s.next pos) (acc.push pos)
    else
      findAllAux s p stopPos (s.next pos) acc
  else acc
termination_by stopPos.1 - pos.1

/-- Find all occurences of a given character -/
@[inline] def findAll (s : String) (p : Char → Bool) : Array Pos :=
  findAllAux s p s.endPos 0

-- TODO: modify `String.get` which currently returns 'A' as default.
def get₂ (s : String) (pos : String.Pos) : Char := match s.get? pos with
  | some c => c
  | none => '\uFFFD'

end String

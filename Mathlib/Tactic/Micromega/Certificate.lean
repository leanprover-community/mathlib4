import Mathlib.Tactic.Micromega.Basic

namespace Micromega

class NumberSpec (α) where
  ofInt : Int → α
  toRat : α → Rat
  zero : α
  unit : α
  mul : α → α → α
  beq : α → α → Bool

instance : NumberSpec Int where
  ofInt := id
  toRat := Rat.ofInt
  zero := 0
  unit := 1
  mul := Int.mul
  beq := (·==·)

instance : NumberSpec Rat where
  ofInt := Rat.ofInt
  toRat := id
  zero := 0
  unit := 1
  mul := (·*·)
  beq := (·==·)

-- def PolyExpr.develop [NumberSpec α] : PolyExpr α → Poly α

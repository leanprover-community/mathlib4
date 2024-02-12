import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.MetaDefs

open Lean Qq

#eval
  let q : ℚ := 3/15
  guard <| toExpr q = q((1/5 : ℚ))

axiom α : Type
axiom h : Field α

attribute [instance] h

#eval do
  let val ← Qq.evalRat q(1/3 - 100/6 : α)
  guard <| val = -49/3

#eval do
  let val ← Qq.evalRat $ (show Q(ℚ) from toExpr (-(5/3) : ℚ))
  guard <| val = -5/3

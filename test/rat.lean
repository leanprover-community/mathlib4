import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.MetaDefs

#eval
  let q : ℚ := 3/15 in
  guard <| (toExpr q) = q((1/5 : ℚ))

constants (α : Type) (h : Field α)

attribute [instance] h

#eval
  guard <| Expr.evalRat `(1/3 - 100/6 : α) = some (-49/3)

#eval
  guard <| (Expr.evalRat $ toExpr (-(5/3) : ℚ)) = some (-5/3)

import Init.Data.Int.Basic
import Lean.Elab
import Lean.ToExpr

open Lean Meta

def intToExpr (n : Int) : Expr :=
let f : Nat → Expr :=
λ n => mkApp3 (mkConst `OfNat.ofNat [levelZero])
  (mkConst `Int)
  (toExpr n)
  (mkApp
    (mkConst `Int.instOfNatInt)
    (toExpr n))
match n with
| Int.ofNat n => f n
| Int.negSucc n => mkApp3
  (mkConst `Neg.neg [levelZero])
  (mkConst `Int)
  (mkConst `Int.instNegInt)
  (f (n + 1))

instance : ToExpr Int :=
{ toExpr := intToExpr,
  toTypeExpr := mkConst `Int }

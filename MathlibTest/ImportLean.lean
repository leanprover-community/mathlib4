module

public import Mathlib

/-
Lean's metaprogramming API is available while elaborating files that import Mathlib, but it should
not be available to runtime declarations unless it is imported explicitly.
-/

/--
error: Invalid definition `foo`, may not access declaration `Lean.Expr.bvar` imported as `meta`; consider adding `import Lean.Expr`
-/
#guard_msgs in
public def foo : Lean.Expr := .bvar 0

-- The same API remains usable during elaboration.
public meta def elaboratedExpr : Lean.Expr := .bvar 0

-- The data API shared with the expression recognizers remains available at runtime.
public def comparison : Mathlib.Ineq := .le

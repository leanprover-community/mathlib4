module

public import Mathlib

/-
Lean's metaprogramming API is available while elaborating files that import Mathlib, but it should
not be available to runtime declarations unless it is imported explicitly.

If this test fails in your PR because `foo` no longer produces an error, you have almost certainly
introduced an ordinary import that exposes Lean's metaprogramming API at runtime through `Mathlib`.
Check your new or changed imports and their transitive dependencies, and change imports used only
for elaboration to `meta import`. Tactic implementations should be marked `meta` and meta-import
their Lean dependencies.
-/

/--
error: Invalid definition `foo`, may not access declaration `Lean.Expr.bvar` imported as `meta`; consider adding `import Lean.Expr`
-/
#guard_msgs in
public def foo : Lean.Expr := .bvar 0

-- The same API remains usable during elaboration.
public meta def elaboratedExpr : Lean.Expr := .bvar 0

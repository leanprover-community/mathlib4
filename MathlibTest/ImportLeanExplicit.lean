module

public import Mathlib
public import Lean.Expr

-- An ordinary import opts into the runtime API.
public def foo : Lean.Expr := .bvar 0

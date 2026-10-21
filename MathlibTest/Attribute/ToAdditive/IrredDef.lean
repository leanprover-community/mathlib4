module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.IrreducibleDef

@[expose] public section

set_option autoImplicit true
@[to_additive]
irreducible_def conj [Group G] (a b : G) := a⁻¹ * b * a

example [AddGroup A] (a b : A) : addConj a b = (-a) + b + a :=
  addConj_def a b

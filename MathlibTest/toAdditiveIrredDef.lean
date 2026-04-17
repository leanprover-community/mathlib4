import Mathlib.Tactic.IrreducibleDef
import Mathlib.Algebra.Group.Defs

set_option autoImplicit true
@[to_additive]
irreducible_def conj [Group G] (a b : G) := a⁻¹ * b * a

example [AddGroup A] (a b : A) : addConj a b = (-a) + b + a :=
  addConj_def a b

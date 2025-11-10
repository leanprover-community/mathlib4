import Mathlib.Tactic.IrreducibleDef
import Mathlib.Algebra.Group.Defs

set_option autoImplicit true
@[to_additive]
irreducible_def mul_conj [Group G] (a b : G) := a⁻¹ * b * a

example [AddGroup A] (a b : A) : add_conj a b = (-a) + b + a :=
  add_conj_def a b

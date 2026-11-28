import Mathlib.Tactic.Simps.Generalized
import Mathlib.Logic.Equiv.Defs

/-! # Tests for `simps!!` -/

/-! ### A generalized projection that is a projection applied to an argument -/

namespace Toy

structure Pointed (α : Type) where
  e : α ≃ Bool
  extra : Bool

/-- The element of `α` corresponding to `false`. -/
@[simps_proj]
abbrev Pointed.pt {α : Type} (p : Pointed α) : α := p.e.symm false

@[simps!!]
def foo : Pointed Bool where
  e := { toFun := not, invFun := not, left_inv := Bool.not_not, right_inv := Bool.not_not }
  extra := true

example : foo.pt = true := foo_pt
example : foo.extra = true := foo_extra
example (a : Bool) : foo.e a = !a := foo_e_apply a

end Toy

/-! ### Errors -/

namespace Toy

/-- A function that is not a morphism. -/
def notAMorphism (n : Nat) : Nat := n

/--
error: `simps_proj`: with `comp` or `precomp`, notAMorphism must be a morphism, but its type is
  Nat
-/
#guard_msgs in
attribute [simps_proj comp] notAMorphism

/-- error: `simps_proj`: notAMorphism has no argument m -/
#guard_msgs in
attribute [simps_proj (self := m)] notAMorphism

/-- error: `simps_proj`: notAMorphism has 1 arguments -/
#guard_msgs in
attribute [simps_proj (self := 2)] notAMorphism

/-- error: Pointed.extra is not a generalized projection (registered with `@[simps_proj]`) -/
#guard_msgs in
initialize_simps_projections!! Pointed (e → extra)

/-- error: f is not a projection of the structure Pointed -/
#guard_msgs in
initialize_simps_projections!! Pointed (f → pt)

end Toy

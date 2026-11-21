import Mathlib.Tactic.Simps.Generalized
import Mathlib.Logic.Equiv.Defs

/-! # Tests for `simps!!` -/

/-! ### A generalized projection that is a projection applied to an argument -/

namespace Toy

structure Pointed (α : Type) where
  e : α ≃ Bool
  extra : Bool

/-- The element of `α` corresponding to `false`. -/
abbrev Pointed.pt {α : Type} (p : Pointed α) : α := p.e.symm false

@[simps_proj (name := pt)]
abbrev Pointed.Simps.pt {α : Type} (p : Pointed α) : α := p.pt

@[simps!!]
def foo : Pointed Bool where
  e := { toFun := not, invFun := not, left_inv := Bool.not_not, right_inv := Bool.not_not }
  extra := true

example : foo.pt = true := foo_pt
example : foo.extra = true := foo_extra
example (a : Bool) : foo.e a = !a := foo_e_apply a

end Toy

/-! ### The unused custom projections linter -/

namespace Toy

structure Pointed' (α : Type) where
  e : α ≃ Bool

@[simps_proj (name := pt)]
abbrev Pointed'.Simps.pt {α : Type} (p : Pointed' α) : α := p.e.symm false

/-- A misspelled custom projection. -/
def Pointed'.Simps.ee {α : Type} (p : Pointed' α) : α ≃ Bool := p.e

-- `Pointed'.Simps.pt` is not reported as unused, but `Pointed'.Simps.ee` is
/--
warning: Not all of the custom declarations [Toy.Pointed'.Simps.ee] are used. Double check the spelling, and use `?` to get more information.

Note: This linter can be disabled with `set_option linter.simpsUnusedCustomDeclarations false`
-/
#guard_msgs in
@[simps!!]
def bar : Pointed' Bool where
  e := { toFun := not, invFun := not, left_inv := Bool.not_not, right_inv := Bool.not_not }

example : bar.e.symm false = true := bar_pt

end Toy

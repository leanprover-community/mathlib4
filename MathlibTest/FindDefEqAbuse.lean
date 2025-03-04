import Mathlib.Tactic.Linter.FindDefEqAbuse

find_defeq_abuse X.Y
namespace X

def Y := Option Nat

--attribute [irreducible] Y

/-- warning: 'Abuse of defeq of '`X.Y' -/
#guard_msgs in
def f : Y := some 0

/-- warning: 'Abuse of defeq of '`X.Y' -/
#guard_msgs in
def g : Y := some 0

theorem f_eq_g : f = g := rfl

theorem d : f = g := by
  unfold f g
  rfl

module

import Mathlib.Init

set_option linter.defeqAbuse true

def NNRat := {r : Rat // 0 ≤ r}

/--
warning: The expected type `NNRat` is different from the structure `Subtype` at implicit transparency.
Such defeq abuse should be avoided as it can cause unification problems.
Instead, consider using a specialized version of `Subtype.mk`.

Note: This linter can be disabled with `set_option linter.defeqAbuse false`
-/
#guard_msgs in
example : NNRat := ⟨1, by decide⟩

-- The linter doesn't fire in proofs
def Ioo (a b x : Nat) := a < x ∧ x < b
example : Ioo 0 2 1 := ⟨by decide, by decide⟩

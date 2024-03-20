-- import Mathlib.Init.Function

-- import Mathlib.Init.Logic



-- open Function

-- #check RightInverse

-- variable (f g : Nat → Nat)

-- example : LeftInverse f g ∧ RightInverse f g := by
--   /- with `Mathlib.Init.Logic`:
--   f g : Nat → Nat
--   ⊢ LeftInverse f g ∧ Function.RightInverse f g
--   -/

--   /- without `Mathlib.Init.Logic`:
--   f g : Nat → Nat
--   ⊢ LeftInverse f g ∧ RightInverse f g
--   -/
--   sorry

import Mathlib.Init.Logic
import Std
import Lean

#check Commutative

#check Std.Commutative
#check Std.Associative
#check Associative
#check left_comm

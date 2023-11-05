/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

-/

import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Meta.WellFoundedTactics

#align_import init.data.nat.gcd from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-!
# Definitions and properties of gcd, lcm, and coprime
-/


open WellFounded

namespace Nat

/-! gcd -/


theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [Nat.gcd_succ]


end Nat

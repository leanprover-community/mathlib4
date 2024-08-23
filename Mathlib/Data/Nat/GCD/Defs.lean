/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Order.Basic

/-!
# Definition of `Nat.Coprime`
-/

namespace Nat

/-!
### `Coprime`

See also `Nat.coprime_of_dvd` and `Nat.coprime_of_dvd'` to prove `Nat.Coprime m n`.
-/

instance (m n : ℕ) : Decidable (Coprime m n) := inferInstanceAs (Decidable (gcd m n = 1))

end Nat

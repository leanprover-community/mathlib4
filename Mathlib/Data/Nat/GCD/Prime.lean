/-
Copyright (c) 2025 Yongshun Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongshun Ye
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Lemmas related to `Nat.Prime`

Some simple lemmas in the module related to `Nat.Prime` that's separated from the others
as they depend on `import Mathlib.Data.Nat.Prime.Defs`.

Currently there are only theorems about a prime number dividing an LCM `p ∣ lcm a b` in this file.
More theorems related to prime number could be added in the future.
-/

namespace Nat

namespace Prime
variable {p a b : ℕ} (hp : Prime p)
include hp

theorem dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b :=
  (dvd_mul hp).mp (h.trans (lcm_dvd_mul a b))

theorem dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

theorem not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b :=
  hp.dvd_lcm.not.mpr <| not_or.mpr ⟨ha, hb⟩

end Prime

end Nat

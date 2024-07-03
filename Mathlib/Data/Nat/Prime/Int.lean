/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/

import Mathlib.Algebra.Ring.Int
import Mathlib.Data.Nat.Prime.Defs


theorem Nat.prime_iff_prime_int {p : ℕ} : p.Prime ↔ _root_.Prime (p : ℤ) :=
  ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast, Int.natAbs_mul, hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]⟩,
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.natCast_ne_zero.1 hp.1,
        (mt Nat.isUnit_iff.1) fun h => by simp [h, not_prime_one] at hp, fun a b => by
        simpa only [Int.natCast_dvd_natCast, (Int.ofNat_mul _ _).symm] using hp.2.2 a b⟩⟩

namespace Int

theorem prime_two : Prime (2 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_two
#align int.prime_two Int.prime_two

theorem prime_three : Prime (3 : ℤ) :=
  Nat.prime_iff_prime_int.mp Nat.prime_three
#align int.prime_three Int.prime_three

end Int

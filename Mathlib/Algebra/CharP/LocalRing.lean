/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic

#align_import algebra.char_p.local_ring from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Characteristics of local rings

## Main result

- `charP_zero_or_prime_power`: In a commutative local ring the characteristics is either
  zero or a prime power.

-/


/-- In a local ring the characteristics is either zero or a prime power. -/
theorem charP_zero_or_prime_power (R : Type*) [CommRing R] [LocalRing R] (q : ℕ)
    [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q := by
  -- Assume `q := char(R)` is not zero.
  apply or_iff_not_imp_left.2
  -- ⊢ ¬q = 0 → IsPrimePow q
  intro q_pos
  -- ⊢ IsPrimePow q
  let K := LocalRing.ResidueField R
  -- ⊢ IsPrimePow q
  haveI RM_char := ringChar.charP K
  -- ⊢ IsPrimePow q
  let r := ringChar K
  -- ⊢ IsPrimePow q
  let n := q.factorization r
  -- ⊢ IsPrimePow q
  -- `r := char(R/m)` is either prime or zero:
  cases' CharP.char_is_prime_or_zero K r with r_prime r_zero
  -- ⊢ IsPrimePow q
  · let a := q / r ^ n
    -- ⊢ IsPrimePow q
    -- If `r` is prime, we can write it as `r = a * q^n` ...
    have q_eq_a_mul_rn : q = r ^ n * a := by rw [Nat.mul_div_cancel' (Nat.ord_proj_dvd q r)]
    -- ⊢ IsPrimePow q
    have r_ne_dvd_a := Nat.not_dvd_ord_compl r_prime q_pos
    -- ⊢ IsPrimePow q
    have rn_dvd_q : r ^ n ∣ q := ⟨a, q_eq_a_mul_rn⟩
    -- ⊢ IsPrimePow q
    rw [mul_comm] at q_eq_a_mul_rn
    -- ⊢ IsPrimePow q
    -- ... where `a` is a unit.
    have a_unit : IsUnit (a : R) := by
      by_contra g
      rw [← mem_nonunits_iff] at g
      rw [← LocalRing.mem_maximalIdeal] at g
      have a_cast_zero := Ideal.Quotient.eq_zero_iff_mem.2 g
      rw [map_natCast] at a_cast_zero
      have r_dvd_a := (ringChar.spec K a).1 a_cast_zero
      exact absurd r_dvd_a r_ne_dvd_a
    -- Let `b` be the inverse of `a`.
    cases' a_unit.exists_left_inv with a_inv h_inv_mul_a
    -- ⊢ IsPrimePow q
    have rn_cast_zero : ↑(r ^ n) = (0 : R) := by
      rw [← @mul_one R _ (r ^ n), mul_comm, ←Classical.choose_spec a_unit.exists_left_inv,
        mul_assoc, ← Nat.cast_mul, ←q_eq_a_mul_rn, CharP.cast_eq_zero R q]
      simp
    have q_eq_rn := Nat.dvd_antisymm ((CharP.cast_eq_zero_iff R q (r ^ n)).mp rn_cast_zero) rn_dvd_q
    -- ⊢ IsPrimePow q
    have n_pos : n ≠ 0 := fun n_zero =>
      absurd (by simpa [n_zero] using q_eq_rn) (CharP.char_ne_one R q)
    -- Definition of prime power: `∃ r n, Prime r ∧ 0 < n ∧ r ^ n = q`.
    exact ⟨r, ⟨n, ⟨r_prime.prime, ⟨pos_iff_ne_zero.mpr n_pos, q_eq_rn.symm⟩⟩⟩⟩
    -- 🎉 no goals
  · haveI K_char_p_0 := ringChar.of_eq r_zero
    -- ⊢ IsPrimePow q
    haveI K_char_zero : CharZero K := CharP.charP_to_charZero K
    -- ⊢ IsPrimePow q
    haveI R_char_zero := RingHom.charZero (LocalRing.residue R)
    -- ⊢ IsPrimePow q
    -- Finally, `r = 0` would lead to a contradiction:
    have q_zero := CharP.eq R char_R_q (CharP.ofCharZero R)
    -- ⊢ IsPrimePow q
    exact absurd q_zero q_pos
    -- 🎉 no goals
#align char_p_zero_or_prime_power charP_zero_or_prime_power

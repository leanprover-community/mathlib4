/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

#align_import number_theory.zsqrtd.quadratic_reciprocity from "leanprover-community/mathlib"@"5b2fe80501ff327b9109fb09b7cc8c325cd0d7d9"

/-!
# Facts about the gaussian integers relying on quadratic reciprocity.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

-/


open Zsqrtd Complex

open scoped ComplexConjugate

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

open PrincipalIdealRing

theorem mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : Fact p.Prime]
    (hpi : Prime (p : ℤ[i])) : p % 4 = 3 :=
  hp.1.eq_two_or_odd.elim
    (fun hp2 =>
      absurd hpi
        (mt irreducible_iff_prime.2 fun ⟨_, h⟩ => by
          have := h ⟨1, 1⟩ ⟨1, -1⟩ (hp2.symm ▸ rfl)
          -- ⊢ False
          rw [← norm_eq_one_iff, ← norm_eq_one_iff] at this
          -- ⊢ False
          exact absurd this (by decide)))
          -- 🎉 no goals
    fun hp1 =>
    by_contradiction fun hp3 : p % 4 ≠ 3 => by
      have hp41 : p % 4 = 1 := by
        rw [← Nat.mod_mul_left_mod p 2 2, show 2 * 2 = 4 from rfl] at hp1
        have := Nat.mod_lt p (show 0 < 4 by decide)
        revert this hp3 hp1
        generalize p % 4 = m
        intros; interval_cases m <;> simp_all -- Porting note: was `decide!`
      let ⟨k, hk⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 <| by rw [hp41]; exact by decide
      -- ⊢ False
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (_ : k' < p), (k' : ZMod p) = k := by
        refine' ⟨k.val, k.val_lt, ZMod.nat_cast_zmod_val k⟩
      have hpk : p ∣ k ^ 2 + 1 := by
        rw [pow_two, ← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
          ← hk, add_left_neg]
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ := by simp [sq, Zsqrtd.ext]
      -- ⊢ False
      have hkltp : 1 + k * k < p * p :=
        calc
          1 + k * k ≤ k + k * k := by
            apply add_le_add_right
            exact (Nat.pos_of_ne_zero fun (hk0 : k = 0) => by clear_aux_decl; simp_all [pow_succ'])
          _ = k * (k + 1) := by simp [add_comm, mul_add]
          _ < p * p := mul_lt_mul k_lt_p k_lt_p (Nat.succ_pos _) (Nat.zero_le _)
      have hpk₁ : ¬(p : ℤ[i]) ∣ ⟨k, -1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, -1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (-1 : ℤ) ≠ 0 by decide <| by simpa [hx0] using congr_arg Zsqrtd.im hx
      have hpk₂ : ¬(p : ℤ[i]) ∣ ⟨k, 1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs <|
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, 1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                show (1 : ℤ) ≠ 0 by decide <| by simpa [hx0] using congr_arg Zsqrtd.im hx
      obtain ⟨y, hy⟩ := hpk
      -- ⊢ False
      have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← Nat.cast_mul p, ← hy]; simp⟩
      -- ⊢ False
      clear_aux_decl
      -- ⊢ False
      tauto
      -- 🎉 no goals
#align gaussian_int.mod_four_eq_three_of_nat_prime_of_prime GaussianInt.mod_four_eq_three_of_nat_prime_of_prime

theorem prime_of_nat_prime_of_mod_four_eq_three (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) :
    Prime (p : ℤ[i]) :=
  irreducible_iff_prime.1 <|
    by_contradiction fun hpi =>
      let ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi
      have : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ p := by
        erw [← ZMod.nat_cast_mod p 4, hp3]; exact by decide
        -- ⊢ ∀ (a b : ZMod 4), a ^ 2 + b ^ 2 ≠ ↑3
                                            -- 🎉 no goals
      this a b (hab ▸ by simp)
                         -- 🎉 no goals
#align gaussian_int.prime_of_nat_prime_of_mod_four_eq_three GaussianInt.prime_of_nat_prime_of_mod_four_eq_three

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
theorem prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [Fact p.Prime] :
    Prime (p : ℤ[i]) ↔ p % 4 = 3 :=
  ⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩
#align gaussian_int.prime_iff_mod_four_eq_three_of_nat_prime GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime

end GaussianInt

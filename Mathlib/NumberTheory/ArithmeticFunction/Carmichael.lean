/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# The Carmichael function

## Main definitions

* `ArithmeticFunction.Carmichael`: the Carmichael function `λ`,
  also known as the reduced totient function.

## Main results

* A formula for `λ n` in terms of the prime factorization of `n`, given by the following theorems:
  `carmichael_two_pow_of_le_two`, `carmichael_two_pow_of_ne_two`, `carmichael_pow_of_prime_ne_two`,
  and `carmichael_factorization`.

## Notation

We use the standard notation `λ` to represent the Carmichael function,
which is accessible in the scope `ArithmeticFunction.Carmichael`.
Since the notation conflicts with the anonymous function notation, it is impossible to use this
notation in statements, but the pretty-printer will use it when showing the goal state.

## Tags

arithmetic functions, totient
-/

@[expose] public section

open Nat Monoid

variable {R : Type*}

namespace ArithmeticFunction

/-- `λ` is the Carmichael function, also known as the reduced totient function,
defined as the exponent of the unit group of `ZMod n`. -/
def Carmichael : ArithmeticFunction ℕ where
  toFun
    | 0 => 0
    | n + 1 => Nat.find <| ExponentExists.of_finite (G := (ZMod (n + 1))ˣ)
  map_zero' := rfl

@[inherit_doc]
scoped[ArithmeticFunction.Carmichael] notation "λ" => ArithmeticFunction.Carmichael

open scoped Carmichael

theorem carmichael_eq_exponent {n : ℕ} (hn : n ≠ 0) : Carmichael n = exponent (ZMod n)ˣ := by
  cases n with | zero => contradiction | succ n =>
  change Nat.find _ = _
  grind [exponent, ExponentExists.of_finite]

/-- This takes in an `NeZero n` instance instead of an `n ≠ 0` hypothesis. -/
theorem carmichael_eq_exponent' (n : ℕ) [NeZero n] : Carmichael n = exponent (ZMod n)ˣ :=
  carmichael_eq_exponent <| NeZero.ne n

@[simp]
theorem pow_carmichael {n : ℕ} (a : (ZMod n)ˣ) : a ^ Carmichael n = 1 := by
  cases n
  · rw [map_zero, pow_zero]
  rw [carmichael_eq_exponent']
  exact pow_exponent_eq_one a

theorem carmichael_dvd_totient (n : ℕ) : Carmichael n ∣ n.totient := by
  cases n
  · simp
  rw [← ZMod.card_units_eq_totient, carmichael_eq_exponent']
  exact Group.exponent_dvd_card

theorem carmichael_dvd {a b : ℕ} (h : a ∣ b) : Carmichael a ∣ Carmichael b := by
  cases b
  · simp
  rw [carmichael_eq_exponent <| ne_zero_of_dvd_ne_zero (by lia) h, carmichael_eq_exponent']
  exact MonoidHom.exponent_dvd <| ZMod.unitsMap_surjective h

theorem carmichael_lcm (a b : ℕ) :
    Carmichael (Nat.lcm a b) = Nat.lcm (Carmichael a) (Carmichael b) := by
  by_cases! h₀ : a = 0 ∨ b = 0
  · grind [Nat.lcm_eq_zero_iff, map_zero]
  apply dvd_antisymm
  · rw [carmichael_eq_exponent h₀.left, carmichael_eq_exponent h₀.right,
      carmichael_eq_exponent <| lcm_ne_zero h₀.left h₀.right, ← lcm_eq_nat_lcm <| exponent _,
      ← exponent_prod, ← exponent_eq_of_mulEquiv .prodUnits]
    exact exponent_dvd_of_monoidHom _ <| Units.map_injective <| ZMod.castHom_injective _
  · have ha := carmichael_dvd <| Nat.dvd_lcm_left a b
    have hb := carmichael_dvd <| Nat.dvd_lcm_right a b
    exact Nat.lcm_dvd ha hb

theorem carmichael_mul {a b : ℕ} (h : Coprime a b) :
    Carmichael (a * b) = Nat.lcm (Carmichael a) (Carmichael b) :=
  h.lcm_eq_mul ▸ carmichael_lcm ..

theorem carmichael_finset_lcm {α : Type*} (s : Finset α) (f : α → ℕ) :
    Carmichael (s.lcm f) = s.lcm (Carmichael ∘ f) := by
  classical
  refine s.induction ?_ fun a s ha ih ↦ ?_
  · exact carmichael_eq_exponent' 1 |>.trans exp_eq_one_of_subsingleton
  rw [Finset.lcm_insert, Finset.lcm_insert, ← ih]
  exact carmichael_lcm ..

theorem carmichael_finset_prod {α : Type*} {s : Finset α} {f : α → ℕ}
    (h : Set.Pairwise s <| Coprime.onFun f) : Carmichael (s.prod f) = s.lcm (Carmichael ∘ f) :=
  s.lcm_eq_prod h ▸ carmichael_finset_lcm ..

theorem carmichael_factorization (n : ℕ) [NeZero n] :
    Carmichael n = n.primeFactors.lcm fun p ↦ Carmichael (p ^ n.factorization p) := by
  nth_rw 1 [← n.factorization_prod_pow_eq_self <| NeZero.ne _]
  exact carmichael_finset_prod pairwise_coprime_pow_primeFactors_factorization.set_of_subtype

theorem carmichael_two_pow_of_le_two_eq_totient {n : ℕ} (hn : n ≤ 2) :
    Carmichael (2 ^ n) = (2 ^ n).totient := by
  rw [carmichael_eq_exponent', ← ZMod.card_units_eq_totient, Fintype.card_eq_nat_card]
  exact IsCyclic.iff_exponent_eq_card.mp <| ZMod.isCyclic_units_two_pow_iff n |>.mpr hn

/-- Note that `2 ^ (n - 1) = 1` when `n = 0`. -/
@[simp]
theorem carmichael_two_pow_of_le_two {n : ℕ} (hn : n ≤ 2) :
    Carmichael (2 ^ n) = 2 ^ (n - 1) := by
  rw [carmichael_two_pow_of_le_two_eq_totient hn]
  interval_cases n <;> decide

/-- Note that `2 ^ (n - 2) = 1` when `n ≤ 1`. -/
@[simp]
theorem carmichael_two_pow_of_ne_two {n : ℕ} (hn : n ≠ 2) :
    Carmichael (2 ^ n) = 2 ^ (n - 2) := by
  by_cases hn' : n ≤ 2
  · grind [carmichael_two_pow_of_le_two]
  refine carmichael_eq_exponent' _ |>.trans <| dvd_antisymm ?_ ?_
  · have hcard : Nat.card (ZMod (2 ^ n))ˣ = 2 ^ (n - 1) := by
      rw [card_eq_fintype_card, ZMod.card_units_eq_totient, totient_prime_pow prime_two <| by lia,
        Nat.add_one_sub_one, mul_one]
    have ⟨k, hk, h⟩ := dvd_prime_pow prime_two |>.mp <| hcard ▸ Group.exponent_dvd_nat_card
    have := IsCyclic.iff_exponent_eq_card.not.mp <| ZMod.isCyclic_units_two_pow_iff n |>.not.mpr hn'
    exact h ▸ Nat.pow_dvd_pow 2 (by grind)
  · let five : (ZMod (2 ^ n))ˣ := ZMod.unitOfCoprime 5 <| gcd_pow_right_of_gcd_eq_one rfl
    rw [← ZMod.orderOf_five (n - 2), show n - 2 + 2 = n by lia,
      show (5 : ZMod (2 ^ n)) = five by rfl, orderOf_units]
    exact order_dvd_exponent five

theorem two_mul_carmichael_two_pow_of_three_le_eq_totient {n : ℕ} (hn : 3 ≤ n) :
    2 * Carmichael (2 ^ n) = (2 ^ n).totient := by
  rw [carmichael_two_pow_of_ne_two, ← pow_succ', totient_prime_pow prime_two]
  all_goals lia

@[simp]
theorem carmichael_pow_of_prime_ne_two {p : ℕ} (n : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) :
    Carmichael (p ^ n) = (p ^ n).totient := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [carmichael_eq_exponent', ← ZMod.card_units_eq_totient, Fintype.card_eq_nat_card]
  exact IsCyclic.iff_exponent_eq_card.mp <| ZMod.isCyclic_units_of_prime_pow p hp hp₂ n

end ArithmeticFunction

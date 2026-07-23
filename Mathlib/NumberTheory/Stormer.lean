/-
Copyright (c) 2026 Alexander Benjamin Worth Burns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Benjamin Worth Burns
-/
module

public import Mathlib.NumberTheory.Pell
public import Mathlib.NumberTheory.SmoothNumbers

import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Størmer's theorem on consecutive smooth numbers

This file proves Størmer's theorem that a positive Pell solution whose
`y`-coordinate has no prime divisor outside the Pell parameter is fundamental.
It then applies this result to bound the number of pairs of consecutive
`s`-factored natural numbers.

## References

* [C. Størmer, *Quelques théorèmes sur l'équation de Pell
  \(x^2-Dy^2=\pm1\) et leurs applications* (1897)][stormer1897]
-/

@[expose] public section

open scoped BigOperators

namespace Nat

namespace Stormer

private lemma choose_three_add_choose_three (n : ℕ) :
    (n + 2).choose 3 + n.choose 3 =
      n + 2 * (n + 1).choose 3 := by
  rw [show n + 2 = (n + 1) + 1 by omega]
  simp only [Nat.choose_succ_succ, Nat.choose_one_right]
  norm_num
  omega

private def natPellSolution {x y d : ℕ}
    (hxy : x ^ 2 = 1 + d * y ^ 2) :
    Pell.Solution₁ (d : ℤ) :=
  Pell.Solution₁.mk (x : ℤ) (y : ℤ) <| by
    have hxy' : (x : ℤ) ^ 2 = 1 + (d : ℤ) * (y : ℤ) ^ 2 := by
      exact_mod_cast hxy
    linarith

@[simp] private lemma natPellSolution_x {x y d : ℕ}
    (hxy : x ^ 2 = 1 + d * y ^ 2) :
    (natPellSolution hxy).x = (x : ℤ) := rfl

@[simp] private lemma natPellSolution_y {x y d : ℕ}
    (hxy : x ^ 2 = 1 + d * y ^ 2) :
    (natPellSolution hxy).y = (y : ℤ) := rfl

/-- The Lucas coefficient occurring in the `y`-coordinate of powers of a Pell solution. -/
def pellY (x : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * x * pellY x (n + 1) - pellY x n

@[simp] lemma pellY_zero (x : ℤ) : pellY x 0 = 0 := rfl

@[simp] lemma pellY_one (x : ℤ) : pellY x 1 = 1 := rfl

lemma pellY_add_two (x : ℤ) (n : ℕ) :
    pellY x (n + 2) = 2 * x * pellY x (n + 1) - pellY x n := rfl

@[simp] lemma pellY_two (x : ℤ) : pellY x 2 = 2 * x := by
  simp [pellY_add_two]

@[simp] lemma pellY_three (x : ℤ) : pellY x 3 = 4 * x ^ 2 - 1 := by
  simp [pellY_add_two]
  ring

private lemma pell_y_pow_add_two {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    (a ^ (n + 2)).y =
      2 * a.x * (a ^ (n + 1)).y - (a ^ n).y := by
  rw [show n + 2 = (n + 1) + 1 by omega, pow_add, pow_one,
    Pell.Solution₁.y_mul, show n + 1 = n + 1 by rfl, pow_succ,
    Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
  ring_nf
  have hy : d * (a ^ n).y * a.y ^ 2 =
      (a ^ n).y * (a.x ^ 2 - 1) := by
    calc
      d * (a ^ n).y * a.y ^ 2 =
          (a ^ n).y * (d * a.y ^ 2) := by ring
      _ = (a ^ n).y * (a.x ^ 2 - 1) := by rw [a.prop_y]
  rw [hy]
  ring

/-- The `y`-coordinate of `a ^ n` is `a.y` times its Lucas coefficient. -/
lemma pell_y_pow_eq_mul_pellY {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    (a ^ n).y = a.y * pellY a.x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
      rw [pell_y_pow_add_two, pellY_add_two, hn, hn1]
      ring

/-- The `y`-coordinate of one power divides that of every exponent multiple. -/
lemma pell_y_pow_dvd_y_pow_mul {d : ℤ}
    (a : Pell.Solution₁ d) (m k : ℕ) :
    (a ^ m).y ∣ (a ^ (m * k)).y := by
  induction k with
  | zero =>
      simp only [mul_zero, pow_zero, Pell.Solution₁.y_one]
      exact dvd_zero _
  | succ k ih =>
      rw [Nat.mul_succ, pow_add, Pell.Solution₁.y_mul]
      exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

lemma pellY_nonneg_and_lt_succ {x : ℤ} (hx : 1 < x) (n : ℕ) :
    0 ≤ pellY x n ∧ pellY x n < pellY x (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnextpos : 0 < pellY x (n + 1) := ih.1.trans_lt ih.2
      have hfactor : 0 ≤ 2 * x - 4 := by omega
      have hmul : 0 ≤ (2 * x - 4) * pellY x (n + 1) :=
        mul_nonneg hfactor hnextpos.le
      rw [show n + 1 + 1 = n + 2 by omega, pellY_add_two]
      constructor
      · exact hnextpos.le
      · nlinarith

lemma pellY_lt_of_lt {x : ℤ} (hx : 1 < x) {m n : ℕ} (hmn : m < n) :
    pellY x m < pellY x n := by
  exact (strictMono_nat_of_lt_succ fun k ↦ (pellY_nonneg_and_lt_succ hx k).2) hmn

lemma natCast_le_pellY {x : ℤ} (hx : 1 < x) (n : ℕ) :
    (n : ℤ) ≤ pellY x n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := (pellY_nonneg_and_lt_succ hx n).2
      push_cast
      omega

lemma natCast_lt_pellY {x : ℤ} (hx : 1 < x) {n : ℕ} (hn : 1 < n) :
    (n : ℤ) < pellY x n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn' : 1 < n
      · have hprev := ih hn'
        have hstep := (pellY_nonneg_and_lt_succ hx n).2
        push_cast at hprev ⊢
        omega
      · have hn_eq : n = 1 := by omega
        subst n
        norm_num [pellY]
        omega

/--
The second-order expansion of the Pell/Lucas coefficient in powers of
`x ^ 2 - 1`.
-/
lemma pellY_eq_second_order (x : ℤ) (n : ℕ) :
    ∃ z : ℤ,
      pellY x n =
        (n : ℤ) * x ^ (n - 1) +
          (n.choose 3 : ℤ) * x ^ (n - 3) * (x ^ 2 - 1) +
            (x ^ 2 - 1) ^ 2 * z := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨0, by simp⟩
  | one =>
      refine ⟨0, ?_⟩
      rw [Nat.choose_eq_zero_of_lt (by omega : 1 < 3)]
      simp
  | more n hn hn1 =>
      rcases hn with ⟨z, hz⟩
      rcases hn1 with ⟨z1, hz1⟩
      by_cases hsmall : n < 3
      · interval_cases n <;>
          refine ⟨0, by norm_num [pellY_add_two, Nat.choose] <;> ring⟩
      · have hx2 : x * x ^ (n - 2) = x ^ (n - 1) := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
        have hx0 : x * x ^ n = x ^ (n + 1) := by
          rw [mul_comm, ← pow_succ]
        have hx4 : x ^ 3 * x ^ (n - 2) = x ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hx5 : x ^ 2 * x ^ (n - 3) = x ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hx6 : x ^ 4 * x ^ (n - 3) = x ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hx7 : x ^ 2 * x ^ (n - 1) = x ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hc :
            (n : ℤ) + 2 * ((n + 1).choose 3 : ℤ) =
              (n.choose 3 : ℤ) + ((n + 2).choose 3 : ℤ) := by
          have h := choose_three_add_choose_three n |>.symm
          exact_mod_cast (by simpa [add_comm] using h)
        have hc' :
            (n : ℤ) + 2 * ((1 + n).choose 3 : ℤ) =
              (n.choose 3 : ℤ) + ((2 + n).choose 3 : ℤ) := by
          simpa only [add_comm] using hc
        refine
          ⟨2 * x * z1 - z + (n.choose 3 : ℤ) * x ^ (n - 3), ?_⟩
        rw [pellY_add_two, hz1, hz]
        push_cast
        ring_nf
        rw [hx0, hx2, hx4, hx5, hx6]
        rw [← hx7]
        have hcm := congrArg
          (fun t : ℤ ↦ t * x ^ (n - 1) * (x ^ 2 - 1)) hc'
        ring_nf at hcm ⊢
        linarith [hcm]

/-- Modulo `x ^ 2 - 1`, a Pell/Lucas coefficient is its first-order term. -/
lemma pellY_eq_add_sq_sub_one_mul (x : ℤ) (n : ℕ) :
    ∃ z : ℤ, pellY x n =
      (n : ℤ) * x ^ (n - 1) + (x ^ 2 - 1) * z := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨0, by simp⟩
  | one => exact ⟨0, by simp⟩
  | more n hn hn1 =>
      rcases hn with ⟨z, hz⟩
      rcases hn1 with ⟨z1, hz1⟩
      cases n with
      | zero =>
          exact ⟨0, by simp [pellY_add_two]⟩
      | succ n =>
          refine ⟨2 * x * z1 - z + (n + 1 : ℕ) * x ^ n, ?_⟩
          rw [pellY_add_two, hz1, hz]
          push_cast
          simp only [pow_succ]
          ring

lemma pellY_modEq_of_dvd_sq_sub_one {x m : ℤ} (n : ℕ)
    (hm : m ∣ x ^ 2 - 1) :
    Int.ModEq m (pellY x n) ((n : ℤ) * x ^ (n - 1)) := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨z, hz⟩ := pellY_eq_add_sq_sub_one_mul x n
  rw [hz]
  have heq :
      (n : ℤ) * x ^ (n - 1) -
          ((n : ℤ) * x ^ (n - 1) + (x ^ 2 - 1) * z) =
        -((x ^ 2 - 1) * z) := by
    ring
  rw [heq]
  exact dvd_neg.mpr (dvd_mul_of_dvd_left hm z)

lemma coprime_x_parameter {x y d : ℕ}
    (h : x ^ 2 = 1 + d * y ^ 2) :
    x.Coprime d := by
  rw [← Nat.coprime_pow_left_iff (n := 2) (by omega)]
  rw [h, Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left d

lemma prime_eq_of_dvd_parameter_and_pellY
    {x y d p q : ℕ} (hxy : x ^ 2 = 1 + d * y ^ 2)
    (hp : p.Prime) (hq : q.Prime) (hqd : q ∣ d)
    (hqc : (q : ℤ) ∣ pellY (x : ℤ) p) :
    q = p := by
  have hdvd : (d : ℤ) ∣ (x : ℤ) ^ 2 - 1 := by
    refine ⟨(y : ℤ) ^ 2, ?_⟩
    linarith
  have hqd' : (q : ℤ) ∣ (d : ℤ) := by exact_mod_cast hqd
  have hmod := pellY_modEq_of_dvd_sq_sub_one
    (x := (x : ℤ)) (m := (q : ℤ)) p (hqd'.trans hdvd)
  have hprod' : (q : ℤ) ∣ (p : ℤ) * (x : ℤ) ^ (p - 1) :=
    Int.modEq_zero_iff_dvd.mp (hmod.symm.trans hqc.modEq_zero_int)
  have hprod : q ∣ p * x ^ (p - 1) := by exact_mod_cast hprod'
  rcases hq.dvd_mul.mp hprod with hqp | hqx
  · exact (Nat.dvd_prime hp).mp hqp |>.resolve_left hq.ne_one
  · have hqx' : q ∣ x := hq.dvd_of_dvd_pow hqx
    exact False.elim
      (hq.ne_one
        (Nat.eq_one_of_dvd_coprimes (coprime_x_parameter hxy) hqx' hqd))

lemma pellY_natAbs_eq_prime_pow
    {x y d p : ℕ} (hxy : x ^ 2 = 1 + d * y ^ 2)
    (hp : p.Prime) (hnz : pellY (x : ℤ) p ≠ 0)
    (hsmooth :
      ∀ q : ℕ, q.Prime → q ∣ (pellY (x : ℤ) p).natAbs → q ∣ d) :
    ∃ k : ℕ, (pellY (x : ℤ) p).natAbs = p ^ k := by
  refine ⟨(pellY (x : ℤ) p).natAbs.primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd (Int.natAbs_ne_zero.mpr hnz) ?_⟩
  intro q hq hqc
  apply prime_eq_of_dvd_parameter_and_pellY hxy hp hq
    (hsmooth q hq hqc)
  exact Int.natAbs_dvd_natAbs.mp hqc

/--
For a prime at least five dividing `x ^ 2 - 1` but not `x`, the
prime-index Lucas coefficient is not divisible by the square of that prime.
-/
lemma prime_sq_not_dvd_pellY
    {x p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpm : (p : ℤ) ∣ (x : ℤ) ^ 2 - 1) (hpx : ¬p ∣ x) :
    ¬(p : ℤ) ^ 2 ∣ pellY (x : ℤ) p := by
  intro hsq
  obtain ⟨z, hz⟩ := pellY_eq_second_order (x : ℤ) p
  have hpchooseNat : p ∣ p.choose 3 :=
    hp.dvd_choose_self (by omega) (by omega)
  have hpchoose : (p : ℤ) ∣ (p.choose 3 : ℤ) := by
    exact_mod_cast hpchooseNat
  rcases hpchoose with ⟨u, hu⟩
  rcases hpm with ⟨v, hv⟩
  have hsecond :
      (p : ℤ) ^ 2 ∣
        (p.choose 3 : ℤ) * (x : ℤ) ^ (p - 3) *
          ((x : ℤ) ^ 2 - 1) := by
    refine ⟨u * (x : ℤ) ^ (p - 3) * v, ?_⟩
    rw [hu, hv]
    ring
  have hthird :
      (p : ℤ) ^ 2 ∣ (((x : ℤ) ^ 2 - 1) ^ 2 * z) := by
    refine ⟨v ^ 2 * z, ?_⟩
    rw [hv]
    ring
  rcases hsq with ⟨w, hw⟩
  rcases hsecond with ⟨s, hs⟩
  rcases hthird with ⟨t, ht⟩
  have hfirst :
      (p : ℤ) ^ 2 ∣ (p : ℤ) * (x : ℤ) ^ (p - 1) := by
    refine ⟨w - s - t, ?_⟩
    calc
      (p : ℤ) * (x : ℤ) ^ (p - 1) =
          pellY (x : ℤ) p -
              (p.choose 3 : ℤ) * (x : ℤ) ^ (p - 3) *
                ((x : ℤ) ^ 2 - 1) -
                (((x : ℤ) ^ 2 - 1) ^ 2 * z) := by rw [hz]; ring
      _ = (p : ℤ) ^ 2 * w - (p : ℤ) ^ 2 * s -
          (p : ℤ) ^ 2 * t := by rw [hw, hs, ht]
      _ = (p : ℤ) ^ 2 * (w - s - t) := by ring
  have hfirstNat : p ^ 2 ∣ p * x ^ (p - 1) := by
    exact_mod_cast hfirst
  have hpdvdPow : p ∣ x ^ (p - 1) := by
    rw [show p ^ 2 = p * p by ring] at hfirstNat
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hfirstNat
  exact hpx (hp.dvd_of_dvd_pow hpdvdPow)

/-- Positivity of a Pell/Lucas coefficient for a positive Pell solution. -/
lemma pellY_pos_of_pell
    {x y d n : ℕ} (hxy : x ^ 2 = 1 + d * y ^ 2)
    (hx : 0 < x) (hy : 0 < y) (hn : n ≠ 0) :
    0 < pellY (x : ℤ) n := by
  let a : Pell.Solution₁ (d : ℤ) :=
    natPellSolution hxy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hpow : 0 < (a ^ k.succ).y :=
    Pell.Solution₁.y_pow_succ_pos
      (by simpa [a] using hx) (by simpa [a] using hy) k
  rw [pell_y_pow_eq_mul_pellY] at hpow
  simpa only [a, natPellSolution_x, natPellSolution_y] using
    (pos_of_mul_pos_right hpow (by positivity : (0 : ℤ) ≤ (y : ℤ)))

private lemma two_le_of_prime_pow_lt {p k c : ℕ} (hp : 1 < p)
    (hc : c = p ^ k) (hpc : p < c) :
    2 ≤ k := by
  subst c
  cases k with
  | zero => simp at hpc; omega
  | succ k =>
      cases k with
      | zero => simp at hpc
      | succ k => omega

/--
A prime-index Pell/Lucas coefficient always has a prime factor outside the
Pell parameter. This is the key arithmetic lemma in Størmer's proof.
-/
theorem exists_prime_dvd_pellY_not_dvd_parameter
    {x y d p : ℕ} (hxy : x ^ 2 = 1 + d * y ^ 2)
    (hx : 1 < x) (hp : p.Prime) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℤ) ∣ pellY (x : ℤ) p ∧ ¬q ∣ d := by
  by_contra h
  have hsmooth :
      ∀ q : ℕ,
        q.Prime → q ∣ (pellY (x : ℤ) p).natAbs → q ∣ d := by
    intro q hq hqc
    by_contra hqd
    exact h ⟨q, hq, Int.natAbs_dvd_natAbs.mp hqc, hqd⟩
  have hy : 0 < y := by
    apply Nat.pos_of_ne_zero
    intro hy
    subst y
    norm_num at hxy
    nlinarith
  have hcpos : 0 < pellY (x : ℤ) p :=
    pellY_pos_of_pell hxy (by omega) hy hp.ne_zero
  obtain ⟨k, hk⟩ :=
    pellY_natAbs_eq_prime_pow hxy hp hcpos.ne' hsmooth
  let c := (pellY (x : ℤ) p).natAbs
  have hceq : (c : ℤ) = pellY (x : ℤ) p :=
    Int.natAbs_of_nonneg hcpos.le
  have hcgtInt : (p : ℤ) < (c : ℤ) := by
    rw [hceq]
    exact natCast_lt_pellY (by exact_mod_cast hx) hp.one_lt
  have hcgt : p < c := by exact_mod_cast hcgtInt
  have hk2 : 2 ≤ k := two_le_of_prime_pow_lt hp.one_lt hk hcgt
  have hcdef : c = p ^ k := by simpa only [c] using hk
  have hpsqNat : p ^ 2 ∣ c := by
    rw [hcdef]
    exact pow_dvd_pow p hk2
  have hpsqInt : (p : ℤ) ^ 2 ∣ pellY (x : ℤ) p := by
    rw [← hceq]
    exact_mod_cast hpsqNat
  have hpdvdC : p ∣ c := by
    rw [hcdef]
    exact dvd_pow_self p (by omega)
  have hpd : p ∣ d := hsmooth p hp hpdvdC
  have hpx : ¬p ∣ x := by
    intro hpx
    exact hp.ne_one
      (Nat.eq_one_of_dvd_coprimes
        (coprime_x_parameter hxy) hpx hpd)
  by_cases hp5 : 5 ≤ p
  · exact (prime_sq_not_dvd_pellY hp hp5
      (by
        have hxy' :
            (x : ℤ) ^ 2 = 1 + (d : ℤ) * (y : ℤ) ^ 2 := by
          exact_mod_cast hxy
        have hdvd : (d : ℤ) ∣ (x : ℤ) ^ 2 - 1 := by
          refine ⟨(y : ℤ) ^ 2, ?_⟩
          linarith
        exact
          (by exact_mod_cast hpd : (p : ℤ) ∣ (d : ℤ)).trans hdvd)
      hpx) hpsqInt
  · have hp_lt : p < 5 := by omega
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p
    · have hfour : 4 ∣ 2 * x := by
        rw [pellY_two] at hpsqInt
        norm_num at hpsqInt
        exact_mod_cast hpsqInt
      have htwo : 2 ∣ x := by
        change 2 * 2 ∣ 2 * x at hfour
        exact (Nat.mul_dvd_mul_iff_left (by omega)).mp hfour
      exact hpx htwo
    · have hAB :
          (2 * x - 1) * (2 * x + 1) = c := by
        apply Nat.cast_injective (R := ℤ)
        rw [hceq]
        push_cast [show 1 ≤ 2 * x by omega]
        rw [pellY_three]
        ring
      have hA : 2 * x - 1 ∣ 3 ^ k := by
        rw [← hcdef, ← hAB]
        exact dvd_mul_right _ _
      have hB : 2 * x + 1 ∣ 3 ^ k := by
        rw [← hcdef, ← hAB]
        exact dvd_mul_left _ _
      obtain ⟨i, -, hi⟩ :=
        (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hA
      obtain ⟨j, -, hj⟩ :=
        (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hB
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        simp at hi
        omega
      have hj0 : j ≠ 0 := by
        intro hj0
        subst j
        simp at hj
        omega
      have hdvdA : 3 ∣ 2 * x - 1 := by
        rw [hi]
        exact dvd_pow_self 3 hi0
      have hdvdB : 3 ∣ 2 * x + 1 := by
        rw [hj]
        exact dvd_pow_self 3 hj0
      have : 3 ∣ 2 := by
        convert Nat.dvd_sub hdvdB hdvdA using 1
        omega
      norm_num at this
    · exact (by decide : ¬Nat.Prime 4) hp

/-- The key arithmetic lemma, specialized to a fundamental Pell solution. -/
lemma exists_prime_dvd_pellY_not_dvd_parameter_of_isFundamental
    {d : ℤ} {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a)
    {p : ℕ} (hp : p.Prime) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℤ) ∣ pellY a.x p ∧ ¬q ∣ d.natAbs := by
  let x := a.x.natAbs
  let y := a.y.natAbs
  let dn := d.natAbs
  have hxcast : (x : ℤ) = a.x :=
    Int.natAbs_of_nonneg (zero_le_one.trans ha.1.le)
  have hycast : (y : ℤ) = a.y :=
    Int.natAbs_of_nonneg ha.2.1.le
  have hdcast : (dn : ℤ) = d :=
    Int.natAbs_of_nonneg ha.d_pos.le
  have hxy : x ^ 2 = 1 + dn * y ^ 2 := by
    exact_mod_cast
      (show (x : ℤ) ^ 2 = 1 + (dn : ℤ) * (y : ℤ) ^ 2 by
        rw [hxcast, hycast, hdcast]
        exact a.prop_x)
  have hx : 1 < x := by
    exact_mod_cast
      (show (1 : ℤ) < (x : ℤ) by rw [hxcast]; exact ha.1)
  simpa only [hxcast, dn] using
    exists_prime_dvd_pellY_not_dvd_parameter hxy hx hp

/--
A positive Pell solution whose `y`-coordinate has no prime factor outside
the Pell parameter equals the fundamental solution.
-/
theorem eq_fundamental_of_primeFactors_y_subset_parameter
    {d : ℤ} {a b : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a)
    (hbx : 1 < b.x) (hby : 0 < b.y)
    (hsmooth :
      ∀ q : ℕ, q.Prime → q ∣ b.y.natAbs → q ∣ d.natAbs) :
    b = a := by
  obtain ⟨n, hbpow⟩ := ha.eq_pow_of_nonneg (by omega) hby.le
  have hn1 : n = 1 := by
    by_contra hn1
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨k, hk⟩ := hpn
    obtain ⟨q, hq, hqpell, hqparameter⟩ :=
      exists_prime_dvd_pellY_not_dvd_parameter_of_isFundamental ha hp
    have hqap : (q : ℤ) ∣ (a ^ p).y := by
      rw [pell_y_pow_eq_mul_pellY]
      exact hqpell.mul_left a.y
    have hqpow : (q : ℤ) ∣ (a ^ n).y := by
      rw [hk]
      exact hqap.trans (pell_y_pow_dvd_y_pow_mul a p k)
    have hqby : (q : ℤ) ∣ b.y := by
      rw [hbpow]
      exact hqpow
    exact hqparameter (hsmooth q hq (Int.natCast_dvd.mp hqby))
  subst n
  simpa using hbpow

/--
Two positive Pell solutions coincide if all prime factors of both
`y`-coordinates divide the Pell parameter.
-/
theorem eq_of_primeFactors_y_subset_parameter
    {d : ℤ} {a b : Pell.Solution₁ d}
    (hax : 1 < a.x) (hay : 0 < a.y)
    (hbx : 1 < b.x) (hby : 0 < b.y)
    (haSmooth :
      ∀ q : ℕ, q.Prime → q ∣ a.y.natAbs → q ∣ d.natAbs)
    (hbSmooth :
      ∀ q : ℕ, q.Prime → q ∣ b.y.natAbs → q ∣ d.natAbs) :
    a = b := by
  obtain ⟨f, hf⟩ :=
    Pell.IsFundamental.exists_of_not_isSquare
      (Pell.Solution₁.d_pos_of_one_lt_x hax)
      (Pell.Solution₁.d_nonsquare_of_one_lt_x hax)
  exact
    (eq_fundamental_of_primeFactors_y_subset_parameter
      hf hax hay haSmooth).trans
    (eq_fundamental_of_primeFactors_y_subset_parameter
      hf hbx hby hbSmooth).symm

/--
Two positive natural-number solutions of the same Pell equation coincide if
all prime factors of both `y`-coordinates divide the Pell parameter.
-/
theorem pell_smooth_x_unique
    {d x₁ y₁ x₂ y₂ : ℕ}
    (hx₁ : 1 < x₁) (hy₁ : 0 < y₁)
    (hxy₁ : x₁ ^ 2 = 1 + d * y₁ ^ 2)
    (hsmooth₁ : ∀ p : ℕ, p.Prime → p ∣ y₁ → p ∣ d)
    (hx₂ : 1 < x₂) (hy₂ : 0 < y₂)
    (hxy₂ : x₂ ^ 2 = 1 + d * y₂ ^ 2)
    (hsmooth₂ : ∀ p : ℕ, p.Prime → p ∣ y₂ → p ∣ d) :
    x₁ = x₂ := by
  have hsol : natPellSolution hxy₁ = natPellSolution hxy₂ := by
    apply eq_of_primeFactors_y_subset_parameter
    · simpa only [natPellSolution_x] using
        (show (1 : ℤ) < (x₁ : ℤ) by exact_mod_cast hx₁)
    · simpa only [natPellSolution_y] using
        (show (0 : ℤ) < (y₁ : ℤ) by exact_mod_cast hy₁)
    · simpa only [natPellSolution_x] using
        (show (1 : ℤ) < (x₂ : ℤ) by exact_mod_cast hx₂)
    · simpa only [natPellSolution_y] using
        (show (0 : ℤ) < (y₂ : ℤ) by exact_mod_cast hy₂)
    · simpa only [natPellSolution_y, Int.natAbs_natCast] using hsmooth₁
    · simpa only [natPellSolution_y, Int.natAbs_natCast] using hsmooth₂
  exact_mod_cast
    (show (x₁ : ℤ) = (x₂ : ℤ) by
      simpa only [natPellSolution_x] using congrArg Pell.Solution₁.x hsol)

/--
The exponent of a prime retained in the Pell parameter in Størmer's
decomposition. It is `0` for exponent zero, `1` for a positive odd exponent,
and `2` for a positive even exponent.
-/
def reducedExponent (e : ℕ) : ℕ :=
  if e = 0 then 0 else if e % 2 = 1 then 1 else 2

lemma reducedExponent_lt_three (e : ℕ) : reducedExponent e < 3 := by
  simp only [reducedExponent]
  split_ifs <;> omega

lemma reducedExponent_le (e : ℕ) : reducedExponent e ≤ e := by
  simp only [reducedExponent]
  split_ifs with hzero hodd
  · omega
  · omega
  · have hmod : e % 2 < 2 := Nat.mod_lt e (by omega)
    omega

lemma reducedExponent_eq_zero_iff (e : ℕ) :
    reducedExponent e = 0 ↔ e = 0 := by
  by_cases h : e = 0
  · simp [reducedExponent, h]
  · by_cases hodd : e % 2 = 1 <;> simp [reducedExponent, h, hodd]

/-- The exponent left after removing `reducedExponent e`, divided by two. -/
def squareExponent (e : ℕ) : ℕ :=
  (e - reducedExponent e) / 2

lemma reducedExponent_add_two_mul_squareExponent (e : ℕ) :
    reducedExponent e + 2 * squareExponent e = e := by
  simp only [reducedExponent, squareExponent]
  split_ifs with hzero hodd
  · omega
  · have hmod : e % 2 < 2 := Nat.mod_lt e (by omega)
    omega
  · have hmod : e % 2 < 2 := Nat.mod_lt e (by omega)
    omega

lemma reducedExponent_pos_of_squareExponent_pos {e : ℕ}
    (h : 0 < squareExponent e) :
    0 < reducedExponent e := by
  rw [pos_iff_ne_zero]
  exact (reducedExponent_eq_zero_iff e).not.mpr fun he ↦ by
    subst e
    simp [squareExponent] at h

/-- Størmer's three-valued exponent code for an `s`-factored number. -/
def exponentCode (s : Finset ℕ) (m : ℕ) : s → Fin 3 :=
  fun p ↦ ⟨reducedExponent (m.factorization p), reducedExponent_lt_three _⟩

/-- The Pell parameter associated to an `s`-factored number. -/
def pellParameter (s : Finset ℕ) (m : ℕ) : ℕ :=
  ∏ p ∈ s, p ^ reducedExponent (m.factorization p)

/-- The square factor associated to an `s`-factored number. -/
def pellSquareFactor (s : Finset ℕ) (m : ℕ) : ℕ :=
  ∏ p ∈ s, p ^ squareExponent (m.factorization p)

lemma prod_factorization_over_superset {s : Finset ℕ} {m : ℕ}
    (hm : m ∈ factoredNumbers s) :
    ∏ p ∈ s, p ^ m.factorization p = m := by
  calc
    ∏ p ∈ s, p ^ m.factorization p =
        m.factorization.prod (fun p e ↦ p ^ e) :=
      (m.factorization.prod_of_support_subset
        (by simpa using primeFactors_subset_of_mem_factoredNumbers hm)
        (fun p e ↦ p ^ e) (by simp)).symm
    _ = m := m.prod_factorization_pow_eq_self hm.1

lemma eq_pellParameter_mul_pellSquareFactor_sq {s : Finset ℕ} {m : ℕ}
    (hm : m ∈ factoredNumbers s) :
    m = pellParameter s m * pellSquareFactor s m ^ 2 := by
  calc
    m = ∏ p ∈ s, p ^ m.factorization p :=
      (prod_factorization_over_superset hm).symm
    _ = ∏ p ∈ s,
        (p ^ reducedExponent (m.factorization p) *
          (p ^ squareExponent (m.factorization p)) ^ 2) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_add, Nat.mul_comm,
        reducedExponent_add_two_mul_squareExponent]
    _ = pellParameter s m * pellSquareFactor s m ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]
      rfl

lemma prime_dvd_pellParameter_of_dvd_pellSquareFactor
    {s : Finset ℕ} {m q : ℕ} (hq : q.Prime)
    (hqm : q ∣ pellSquareFactor s m) :
    q ∣ pellParameter s m := by
  rw [pellSquareFactor] at hqm
  obtain ⟨p, hpS, hqp⟩ :=
    (hq.prime.dvd_finsetProd_iff fun p ↦ p ^ squareExponent (m.factorization p)).mp hqm
  have hsquare : 0 < squareExponent (m.factorization p) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have : q ∣ 1 := by simpa [hzero] using hqp
    exact hq.not_dvd_one this
  have hqp' : q ∣ p := hq.dvd_of_dvd_pow hqp
  rw [pellParameter]
  exact (hqp'.trans (dvd_pow_self p
    (reducedExponent_pos_of_squareExponent_pos hsquare).ne')).trans
      (Finset.dvd_prod_of_mem
        (fun p ↦ p ^ reducedExponent (m.factorization p)) hpS)

lemma pellParameter_eq_of_exponentCode_eq {s : Finset ℕ} {m n : ℕ}
    (h : exponentCode s m = exponentCode s n) :
    pellParameter s m = pellParameter s n := by
  apply Finset.prod_congr rfl
  intro p hp
  have := congrFun h ⟨p, hp⟩
  exact congrArg (fun e : Fin 3 ↦ p ^ e.val) this

/-- The number one less than `(2 * n + 1) ^ 2` used in Størmer's reduction. -/
def consecutivePellNumber (n : ℕ) : ℕ :=
  4 * n * (n + 1)

/-- The exponent code attached to a pair of consecutive factored numbers. -/
def consecutiveCode (s : Finset ℕ) (n : ℕ) : s → Fin 3 :=
  exponentCode s (consecutivePellNumber n)

lemma consecutivePellNumber_mem_factoredNumbers {s : Finset ℕ} {n : ℕ}
    (h2 : 2 ∈ s) (hn : n ∈ factoredNumbers s)
    (hn1 : n + 1 ∈ factoredNumbers s) :
    consecutivePellNumber n ∈ factoredNumbers s := by
  have hprod := mul_mem_factoredNumbers hn hn1
  have hpow := pow_mul_mem_factoredNumbers (by norm_num : Nat.Prime 2) 2 hprod
  rw [Finset.insert_eq_of_mem h2] at hpow
  simpa [consecutivePellNumber, pow_two, mul_assoc] using hpow

lemma consecutivePellNumber_eq_pellParameter_mul_sq
    {s : Finset ℕ} {n : ℕ}
    (h2 : 2 ∈ s) (hn : n ∈ factoredNumbers s)
    (hn1 : n + 1 ∈ factoredNumbers s) :
    consecutivePellNumber n =
      pellParameter s (consecutivePellNumber n) *
        pellSquareFactor s (consecutivePellNumber n) ^ 2 :=
  eq_pellParameter_mul_pellSquareFactor_sq
    (consecutivePellNumber_mem_factoredNumbers h2 hn hn1)

lemma consecutive_pell_equation
    {s : Finset ℕ} {n : ℕ}
    (h2 : 2 ∈ s) (hn : n ∈ factoredNumbers s)
    (hn1 : n + 1 ∈ factoredNumbers s) :
    (2 * n + 1) ^ 2 =
      1 + pellParameter s (consecutivePellNumber n) *
        pellSquareFactor s (consecutivePellNumber n) ^ 2 := by
  rw [← consecutivePellNumber_eq_pellParameter_mul_sq h2 hn hn1]
  simp only [consecutivePellNumber]
  ring

lemma pellSquareFactor_pos_of_consecutive
    {s : Finset ℕ} {n : ℕ}
    (h2 : 2 ∈ s) (hn : n ∈ factoredNumbers s)
    (hn1 : n + 1 ∈ factoredNumbers s) :
    0 < pellSquareFactor s (consecutivePellNumber n) := by
  have hdecomp :=
    consecutivePellNumber_eq_pellParameter_mul_sq h2 hn hn1
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn.1
  have hmpos : 0 < consecutivePellNumber n := by
    simp only [consecutivePellNumber]
    positivity
  have hmulpos :
      0 < pellParameter s (consecutivePellNumber n) *
        pellSquareFactor s (consecutivePellNumber n) ^ 2 := by
    rwa [← hdecomp]
  have hy2pos : 0 < pellSquareFactor s (consecutivePellNumber n) ^ 2 :=
    pos_of_mul_pos_right hmulpos (Nat.zero_le _)
  exact (pow_pos_iff (by omega)).mp hy2pos

/--
Størmer's three-valued exponent code is injective on consecutive
`s`-factored pairs.
-/
lemma consecutive_eq_of_consecutiveCode_eq
    {s : Finset ℕ} {m n : ℕ}
    (h2 : 2 ∈ s)
    (hm : m ∈ factoredNumbers s) (hm1 : m + 1 ∈ factoredNumbers s)
    (hn : n ∈ factoredNumbers s) (hn1 : n + 1 ∈ factoredNumbers s)
    (hcode : consecutiveCode s m = consecutiveCode s n) :
    m = n := by
  have hparameter :
      pellParameter s (consecutivePellNumber m) =
        pellParameter s (consecutivePellNumber n) :=
    pellParameter_eq_of_exponentCode_eq hcode
  have hxm : 1 < 2 * m + 1 := by
    have := Nat.pos_of_ne_zero hm.1
    omega
  have hxn : 1 < 2 * n + 1 := by
    have := Nat.pos_of_ne_zero hn.1
    omega
  have hx :
      2 * m + 1 = 2 * n + 1 := by
    apply pell_smooth_x_unique
        (d := pellParameter s (consecutivePellNumber m))
        (y₁ := pellSquareFactor s (consecutivePellNumber m))
        (y₂ := pellSquareFactor s (consecutivePellNumber n))
    · exact hxm
    · exact pellSquareFactor_pos_of_consecutive h2 hm hm1
    · exact consecutive_pell_equation h2 hm hm1
    · intro p hp hpdvd
      exact prime_dvd_pellParameter_of_dvd_pellSquareFactor hp hpdvd
    · exact hxn
    · exact pellSquareFactor_pos_of_consecutive h2 hn hn1
    · simpa only [hparameter] using consecutive_pell_equation h2 hn hn1
    · intro p hp hpdvd
      rw [hparameter]
      exact prime_dvd_pellParameter_of_dvd_pellSquareFactor hp hpdvd
  omega

/-- The Størmer codes whose values contain at least one odd reduced exponent. -/
def AdmissibleCode (s : Finset ℕ) :=
  {f : s → Fin 3 // ∃ p : s, f p = 1}

noncomputable instance (s : Finset ℕ) : Fintype (AdmissibleCode s) := by
  classical
  unfold AdmissibleCode
  infer_instance

private def nonAdmissibleCodeEquiv (s : Finset ℕ) :
    {f : s → Fin 3 // ¬∃ p : s, f p = 1} ≃ (s → Fin 2) :=
  (Equiv.subtypeEquivRight fun f ↦ by simp).trans <|
    Equiv.subtypePiEquivPi.trans <|
      Equiv.piCongrRight fun _ ↦ (finSuccAboveEquiv (1 : Fin 3)).symm

lemma card_admissibleCode (s : Finset ℕ) :
    Fintype.card (AdmissibleCode s) = 3 ^ s.card - 2 ^ s.card := by
  classical
  let P : (s → Fin 3) → Prop := fun f ↦ ∃ p : s, f p = 1
  have hcomp :
      Fintype.card {f : s → Fin 3 // ¬P f} = 2 ^ s.card := by
    calc
      Fintype.card {f : s → Fin 3 // ¬P f} =
          Fintype.card (s → Fin 2) := by
        apply Fintype.card_congr
        simpa only [P] using nonAdmissibleCodeEquiv s
      _ = 2 ^ s.card := by simp
  have hcompl := Fintype.card_subtype_compl P
  have hle := Fintype.card_subtype_le P
  change Fintype.card {f : s → Fin 3 // P f} =
    3 ^ s.card - 2 ^ s.card
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at hcompl hle
  omega

/--
The exponent code of a positive pair of consecutive `s`-factored numbers
contains a `1`. Otherwise its Pell parameter would be a square, contrary to
the non-square parameter of a nontrivial Pell solution.
-/
lemma consecutiveCode_admissible
    {s : Finset ℕ} {n : ℕ}
    (h2 : 2 ∈ s)
    (hn : n ∈ factoredNumbers s)
    (hn1 : n + 1 ∈ factoredNumbers s) :
    ∃ p : s, consecutiveCode s n p = 1 := by
  by_contra hcode
  have hsquareNat :
      IsSquare (pellParameter s (consecutivePellNumber n)) := by
    rw [pellParameter]
    apply Finset.isSquare_prod
    intro p hp
    apply Even.isSquare_pow
    have hne :
        reducedExponent ((consecutivePellNumber n).factorization p) ≠ 1 := by
      intro heq
      apply hcode
      refine ⟨⟨p, hp⟩, ?_⟩
      apply Fin.ext
      change reducedExponent ((consecutivePellNumber n).factorization p) = 1
      exact heq
    have hlt :=
      reducedExponent_lt_three
        ((consecutivePellNumber n).factorization p)
    interval_cases hred :
      reducedExponent ((consecutivePellNumber n).factorization p) <;>
      simp_all
  have hsquareInt :
      IsSquare (pellParameter s (consecutivePellNumber n) : ℤ) :=
    hsquareNat.map (Nat.castRingHom ℤ)
  let a : Pell.Solution₁
      (pellParameter s (consecutivePellNumber n) : ℤ) :=
    natPellSolution (consecutive_pell_equation h2 hn hn1)
  have hax : 1 < a.x := by
    simp only [a, natPellSolution_x]
    exact_mod_cast (show 1 < 2 * n + 1 by
      have := Nat.pos_of_ne_zero hn.1
      omega)
  exact (Pell.Solution₁.d_nonsquare_of_one_lt_x hax) hsquareInt

/--
Refined Størmer bound: among the `3 ^ s.card` exponent codes, the
`2 ^ s.card` codes taking only the values zero and two cannot arise.
-/
theorem card_consecutive_factoredNumbers_le_sub
    {s A : Finset ℕ}
    (h2 : 2 ∈ s)
    (hA : ∀ n ∈ A, n ∈ factoredNumbers s ∧ n + 1 ∈ factoredNumbers s) :
    A.card ≤ 3 ^ s.card - 2 ^ s.card := by
  let encode : A → AdmissibleCode s := fun n ↦
    ⟨consecutiveCode s n,
      consecutiveCode_admissible h2 (hA n n.2).1 (hA n n.2).2⟩
  have hinjective : Function.Injective encode := by
    intro m n hmn
    apply Subtype.ext
    exact consecutive_eq_of_consecutiveCode_eq h2
      (hA m m.2).1 (hA m m.2).2
      (hA n n.2).1 (hA n n.2).2
      (congrArg Subtype.val hmn)
  calc
    A.card = Fintype.card A := by simp
    _ ≤ Fintype.card (AdmissibleCode s) :=
      Fintype.card_le_of_injective encode hinjective
    _ = 3 ^ s.card - 2 ^ s.card := card_admissibleCode s

/--
A finite collection of positive consecutive `s`-factored pairs has
cardinality at most `3 ^ s.card`.
-/
theorem card_consecutive_factoredNumbers_le
    {s A : Finset ℕ}
    (h2 : 2 ∈ s)
    (hA : ∀ n ∈ A, n ∈ factoredNumbers s ∧ n + 1 ∈ factoredNumbers s) :
    A.card ≤ 3 ^ s.card := by
  exact (card_consecutive_factoredNumbers_le_sub h2 hA).trans (Nat.sub_le _ _)

end Stormer

end Nat

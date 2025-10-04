/-
Copyright (c) 2025 Concordance dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle AI, Yury Kudryashov
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.IntervalCases

open scoped Nat BigOperators

set_option maxHeartbeats 1000000 in
/--
For a prime number $p \ge 5$, the following congruence holds:
$$
\binom{2p-1}{p-1} \equiv 1 \pmod{p^3}
$$
This is equivalent to the following two congruences:
$$
\sum_{k=1}^{p-1} \frac{1}{k} \equiv 0 \
-/
theorem Nat.Prime.two_mul_sub_one_choose_sub_one_modEq_one {p : ℕ} (hp : Nat.Prime p)
    (hp_ge_5 : p ≥ 5) :
    choose (2 * p - 1) (p - 1) ≡ 1 [MOD p^3] := by
  haveI := Fact.mk hp;
  -- Using the identity ${2p-1 \choose p-1} = {2p \choose p} / 2$, we rewrite the goal.
  have h_binom : choose (2 * p - 1) (p - 1) = choose (2 * p) p / 2 := by
    -- Using the identity ${2p \choose p} = {2p-1 \choose p-1} + {2p-1 \choose p}$
    -- and the symmetry property ${2p-1 \choose p} = {2p-1 \choose p-1}$,
    -- we can derive the desired result.
    have h_identity : choose (2 * p) p = choose (2 * p - 1) (p - 1) + choose (2 * p - 1) p := by
      cases p <;> trivial;
    have h_symmetry : choose (2 * p - 1) p = choose (2 * p - 1) (p - 1) := by
      rw [choose_symm_of_eq_add]
      omega
    simp +arith +decide [h_identity, h_symmetry]
  rw [h_binom]
  -- Using the identity ${2p \choose p} = \sum_{k=0}^{p} {p \choose k}^2$, we rewrite the goal.
  have h_binom' : choose (2 * p) p = ∑ k ∈ Finset.range (p + 1), choose p k ^ 2 := by
    rw [Nat.two_mul, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => choose p i * choose p j]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [sq, choose_symm (Finset.mem_range_succ_iff.mp hx)]
  -- We need to show that $\sum_{k=1}^{p-1} \binom{p}{k}^2 \equiv 0 \pmod{p^3}$.
  have h_sum : ∑ k ∈ Finset.Ico 1 p, choose p k ^ 2 ≡ 0 [MOD p^3] := by
    -- Since $\binom{p}{k}$ is divisible by $p$ for $1 \leq k \leq p-1$,
    -- we have $\binom{p}{k}^2 \equiv 0 \pmod{p^2}$.
    have h_div : ∀ k ∈ Finset.Ico 1 p, choose p k ^ 2 ≡ 0 [MOD p^2] := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [modEq_zero_iff_dvd]
      gcongr
      apply hp.dvd_choose_self <;> omega
    -- Since $\binom{p}{k}^2 \equiv 0 \pmod{p^2}$, we can factor out $p^2$ from the sum.
    have h_factor : ∑ k ∈ Finset.Ico 1 p, choose p k ^ 2 ≡
        p^2 * ∑ k ∈ Finset.Ico 1 p, (choose p k / p) ^ 2 [MOD p^3] := by
      have h_factor : ∀ k ∈ Finset.Ico 1 p, choose p k ^ 2 = p^2 * (choose p k / p) ^ 2 := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [← mul_pow, Nat.mul_div_cancel' (hp.dvd_choose_self (by omega) (by omega))]
      rw [Finset.mul_sum _ _ _, Finset.sum_congr rfl h_factor]
    refine h_factor.trans <| Nat.modEq_zero_iff_dvd.mpr ?_;
    -- We need to show that $\sum_{k=1}^{p-1} \left(\frac{\binom{p}{k}}{p}\right)^2$
    -- is divisible by $p$.
    have h_sum_div : p ∣ ∑ k ∈ Finset.Ico 1 p, (choose p k / p) ^ 2 := by
      -- Using the identity $\binom{p}{k} = \frac{p}{k} \binom{p-1}{k-1}$,
      -- we can rewrite $\frac{\binom{p}{k}}{p}$ as $\frac{\binom{p-1}{k-1}}{k}$.
      have h_identity : ∀ k ∈ Finset.Ico 1 p, choose p k / p = choose (p - 1) (k - 1) / k := by
        intros k hk;
        rcases p with (_ | _ | p) <;> rcases k with (_ | _ | k) <;> simp_all +decide
        -- By definition of binomial coefficients, we can rewrite both sides using factorials.
        have h_factorial : (p + 2).choose (k + 2) = (p + 2)! / ((k + 2)! * (p - k)!) ∧
            (p + 1).choose (k + 1) = (p + 1)! / ((k + 1)! * (p - k)!) := by
          simp +decide [choose_eq_factorial_div_factorial (by linarith : k + 2 ≤ p + 2),
            choose_eq_factorial_div_factorial (by linarith : k + 1 ≤ p + 1)]
        simp_all +decide [Nat.factorial_succ, mul_comm, mul_left_comm, Nat.div_div_eq_div_mul]
        rw [show p ! * (( p + 1) * (p + 1 + 1)) = (p ! * (p + 1)) * (p + 1 + 1) by ring,
          show k ! * (( p - k) ! * (( k + 1) * (( p + 1 + 1) * (k + 1 + 1)))) =
            (k ! * (( p - k) ! * (( k + 1) * (k + 1 + 1)))) * (p + 1 + 1) by ring,
          Nat.mul_div_mul_right _ _ (Nat.succ_pos _)]
      -- Using the identity $\binom{p-1}{k-1} \equiv (-1)^{k-1} \pmod{p}$, we can rewrite the sum.
      have h_cong : ∀ k ∈ Finset.Ico 1 p, choose (p - 1) (k - 1) ≡ (-1) ^ (k - 1) [ZMOD p] := by
        intro k hk
        rw [← ZMod.intCast_eq_intCast_iff]
        simp_all only [Finset.mem_Ico, and_imp, Int.cast_natCast, Int.reduceNeg, Int.cast_pow,
          Int.cast_neg, Int.cast_one]
        obtain ⟨left, right⟩ := hk
        induction left <;> aesop
        rcases m <;> aesop
        rw [_root_.pow_succ']
        rw [← a_ih (by linarith), neg_one_mul]
        rw [eq_neg_iff_add_eq_zero]
        -- Using Pascal's rule, we have $(p-1 choose n+1) + (p-1 choose n) = (p choose n+1)$.
        have h_pascal : (p - 1).choose (n + 1) + (p - 1).choose n = p.choose (n + 1) := by
          cases p <;> simp_all +arith +decide [choose]
        norm_cast ; aesop;
        rw [ZMod.natCast_eq_zero_iff] ; exact hp.dvd_choose_self (by linarith) (by linarith)
      -- Therefore, the sum of $(k⁻¹)^2$ over $k$ from $1$ to $p-1$
      -- is congruent to the sum of $k^2$ over $k$ from $1$ to $p-1$ modulo $p$.
      have h_sum_cong : ∑ k ∈ Finset.Ico 1 p, (k⁻¹ : ZMod p) ^ 2 =
          ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 := by
        have h_sum_cong : ∑ k ∈ Finset.univ.erase 0, (k⁻¹ : ZMod p) ^ 2 =
            ∑ k ∈ Finset.univ.erase 0, (k : ZMod p) ^ 2 := by
          apply Finset.sum_bij (fun k _ => k⁻¹);
          -- Case 1
          · simp;
          -- Case 2
          · aesop;
          -- Case 3
          · exact fun b hb => ⟨ b⁻¹, by aesop ⟩;
          -- Case 4
          · simp;
        simp +zetaDelta at *;
        rw [Finset.sum_Ico_eq_sub _ hp.pos, Finset.sum_Ico_eq_sub _ hp.pos]
        simp_all +decide [Finset.sum_range]
        rcases p with (_ | _ | p) <;> simp_all +decide [Fin.sum_univ_succ, ZMod]
      -- Therefore, the sum of $(k⁻¹)^2$ over $k$ from $1$ to $p-1$ is congruent to $0$ modulo $p$.
      have h_sum_zero : ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 = 0 := by
        -- The sum of squares of the first $p-1$ natural numbers
        -- is given by $\frac{(p-1)p(2p-1)}{6}$.
        have h_sum_formula : ∑ k ∈ Finset.Ico 1 p, (k : ℕ) ^ 2 = (p - 1) * p * (2 * p - 1) / 6 :=
          .symm <| Nat.div_eq_of_eq_mul_left (by decide) <| Nat.recOn p (by norm_num) fun n ih => by
            cases n <;> norm_num [Finset.sum_Ico_succ_top, Nat.mul_succ] at *; linarith
        norm_cast;
        rw [h_sum_formula, Nat.cast_div]
        -- Case 1
        · norm_num [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        -- Case 2
        · norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
          rw [← Nat.mod_add_div p 6]
          have := Nat.mod_lt p (by decide : 6 > 0)
          interval_cases p % 6 <;> norm_num [Nat.add_mod, two_mul, add_assoc]
        -- Case 3
        · aesop?;
          rcases p with (_ | _ | _ | _ | _ | _ | _ | p) <;> cases a <;> contradiction;
      simp +zetaDelta at *;
      rw [← ZMod.natCast_eq_zero_iff] ; aesop;
      convert h_sum_cong using 2;
      aesop;
      rw [Nat.cast_div]
      -- Case 1
      · haveI := Fact.mk hp; simp_all +decide [← ZMod.intCast_eq_intCast_iff] ;
        ring_nf; aesop;
      -- Case 2
      · rcases p with (_ | _ | p) <;> rcases x with (_ | _ | x) <;> simp_all +decide
        have := Nat.succ_mul_choose_eq (p + 1) (x + 1);
        -- Since $p + 2$ is prime and $x + 2$ is less than $p + 2$, $x + 2$ and $p + 2$ are coprime.
        have h_coprime : Nat.gcd (x + 2) (p + 2) = 1 :=
          Nat.Coprime.symm <| hp.coprime_iff_not_dvd.mpr <|
            Nat.not_dvd_of_pos_of_lt (by linarith) <| by linarith
        exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime <| this.symm ▸ dvd_mul_left _ _
      -- Case 3
      · rw [Ne.eq_def, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt left right
    -- Since $p$ divides the sum, we can write the sum as $p \cdot m$ for some integer $m$.
    obtain ⟨m, hm⟩ : ∃ m, ∑ k ∈ Finset.Ico 1 p, (choose p k / p) ^ 2 = p * m := h_sum_div;
    exact ⟨ m, by rw [hm] ; ring ⟩;
  -- Since $\sum_{k=1}^{p-1} \binom{p}{k}^2 \equiv 0 \pmod{p^3}$,
  -- we have $\binom{2p}{p} \equiv 2 \pmod{p^3}$.
  have h_cong : choose (2 * p) p ≡ 2 [MOD p^3] := by
    -- Since $\sum_{k=0}^{p} \binom{p}{k}^2 = \binom{2p}{p}$
    -- and $\sum_{k=1}^{p-1} \binom{p}{k}^2 \equiv 0 \pmod{p^3}$,
    -- we have $\binom{2p}{p} \equiv 2 \pmod{p^3}$.
    have h_cong : ∑ k ∈ Finset.range (p + 1), choose p k ^ 2 ≡ 2 [MOD p^3] := by
      rw [Finset.sum_range_succ]
      simp
      rw [Finset.sum_Ico_eq_sum_range] at h_sum;
      rcases p <;> simp_all +decide [add_comm, Finset.sum_range_succ']
      convert h_sum.add_left 2 using 1 ; ring;
    exact h_binom' ▸ h_cong;
  rw [Nat.ModEq] at *;
  -- Since $(2p choose p)$ is even, we can write it as $2k$ for some integer $k$.
  obtain ⟨k, hk⟩ : ∃ k, choose (2 * p) p = 2 * k := by
    have h_even : Even (choose (2 * p) p) := by
      rcases p with (_ | _ | p) <;> simp +arith +decide [parity_simps] at *;
      rw [choose_succ_succ]
      rw [choose_symm_of_eq_add] <;> simp +arith +decide;
    exact even_iff_two_dvd.mp h_even;
  norm_num [hk]
  norm_num [hk] at *
  rw [Nat.ModEq.symm]
  rw [Nat.modEq_iff_dvd]
  -- Since $2(k - 1)$ is divisible by $p^3$ and $p^3$ is odd,
  -- it follows that $k - 1$ is divisible by $p^3$.
  have h_div : (p ^ 3 : ℤ) ∣ 2 * (k - 1) := by
    refine ⟨ 2 * k / p ^ 3 - 2 / p ^ 3, ?_⟩
    linarith [Nat.mod_add_div (2 * k) (p ^ 3), Nat.mod_add_div 2 (p ^ 3)]
  norm_num +zetaDelta at *;
  convert Int.dvd_of_dvd_mul_right_of_gcd_one h_div _ using 1;
  exact_mod_cast Nat.Coprime.pow_left 3 (hp.coprime_iff_not_dvd.mpr fun h => by
    have := Nat.le_of_dvd (by decide) h
    interval_cases p)

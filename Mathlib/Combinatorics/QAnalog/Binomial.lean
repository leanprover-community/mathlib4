/-
Copyright (c) 2026 Eugenio Cainelli, Alessandro Iraci, Lorenzo Luccioli, Giovanni Paolini,
Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eugenio Cainelli, Alessandro Iraci, Lorenzo Luccioli, Giovanni Paolini,
Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.QAnalog.Basic
public import Mathlib.Tactic.Abel

/-!
# `q`-binomial coefficients

This file defines the `q`-binomial coefficients (Gaussian binomial coefficients) and proves
their basic properties.

As in `QAnalog.Basic`, no commutativity is assumed: the `q`-binomial coefficients are
polynomials in the single element `q`, so all the elements occurring in the identities below
commute with each other, which is recorded by the `Commute.qBinomial_right` family of lemmas.
The `q`-binomial theorem involves a second element `x`, and is proved under the hypothesis
`Commute q x`.

## Main definitions

* `qBinomial q n k`, the `q`-binomial coefficient `[n choose k]_q`, defined by the `q`-Pascal
  recursion so that it makes sense over an arbitrary semiring.

## Main results

* `qBinomial_succ_succ`, `qBinomial_succ_succ'`: the two `q`-Pascal recursions.
* `qBinomial_symm`: `[n choose n - k]_q = [n choose k]_q`.
* `qBinomial_mul_qFactorial_mul_qFactorial`: `[n choose k]_q [k]_q ! [n - k]_q ! = [n]_q !`.
* `qBinomial_one_left`: at `q = 1` one recovers the usual binomial coefficient.
* `Commute.list_prod_one_add_pow_mul`: the `q`-binomial theorem
  `∏_{i < n} (1 + q ^ i x) = ∑_k q ^ (k choose 2) [n choose k]_q x ^ k`, for commuting `q` and
  `x`, together with its two standard specialisations
  `prod_one_add_pow_mul_eq_sum_qBinomial` (over a commutative semiring) and
  `Commute.qPochhammer_eq_sum_qBinomial` (in terms of the `q`-Pochhammer symbol).
-/

open Finset Nat

variable {R S : Type*}

section Semiring
variable [Semiring R] (q : R) (m n k : ℕ)

/-- The `q`-binomial coefficient `[n choose k]_q`, also known as a Gaussian binomial
coefficient.  It is defined by the `q`-Pascal recursion
`[n + 1 choose k + 1]_q = [n choose k]_q + q ^ (k + 1) * [n choose k + 1]_q`; equivalently it is
`[n]_q ! / ([k]_q ! [n - k]_q !)`, see `qBinomial_mul_qFactorial_mul_qFactorial`. -/
def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)

@[simp] theorem qBinomial_zero_right : qBinomial q n 0 = 1 := by cases n <;> rfl

@[simp] theorem qBinomial_zero_succ : qBinomial q 0 (k + 1) = 0 := rfl

/-- The `q`-Pascal recursion
`[n + 1 choose k + 1]_q = [n choose k]_q + q ^ (k + 1) [n choose k + 1]_q`. -/
theorem qBinomial_succ_succ :
    qBinomial q (n + 1) (k + 1) = qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1) := rfl

theorem qBinomial_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → qBinomial q n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [qBinomial_succ_succ, qBinomial_eq_zero_of_lt (by omega),
      qBinomial_eq_zero_of_lt (by omega), mul_zero, add_zero]

@[simp] theorem qBinomial_self : qBinomial q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qBinomial_succ_succ, ih, qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n), mul_zero, add_zero]

@[simp] theorem qBinomial_one_right : qBinomial q n 1 = qNat q n := by
  induction n with
  | zero => simp
  | succ n ih => rw [show (1 : ℕ) = 0 + 1 from rfl, qBinomial_succ_succ, ih, qNat_succ']; simp

/-! ### Commutation -/

/-- Anything commuting with `q` commutes with `[n choose k]_q`. -/
theorem Commute.qBinomial_right {q a : R} (h : Commute a q) (n k : ℕ) :
    Commute a (qBinomial q n k) := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => exact (ih k).add_right ((h.pow_right (k + 1)).mul_right (ih (k + 1)))

/-- Anything commuting with `q` commutes with `[n choose k]_q`. -/
theorem Commute.qBinomial_left {q a : R} (h : Commute q a) (n k : ℕ) :
    Commute (qBinomial q n k) a := (h.symm.qBinomial_right n k).symm

theorem qBinomial_commute : Commute q (qBinomial q n k) := (Commute.refl q).qBinomial_right n k

theorem qBinomial_commute_pow : Commute (q ^ m) (qBinomial q n k) :=
  ((Commute.refl q).pow_left m).qBinomial_right n k

theorem qNat_commute_qBinomial : Commute (qNat q m) (qBinomial q n k) :=
  (qBinomial_commute q n k).qNat_left m

theorem qFactorial_commute_qBinomial : Commute (qFactorial q m) (qBinomial q n k) :=
  (qBinomial_commute q n k).qFactorial_left m

/-! ### The second `q`-Pascal recursion, symmetry, and the factorial formula -/

/-- The second `q`-Pascal recursion
`[n + 1 choose k + 1]_q = [n choose k + 1]_q + q ^ (n - k) [n choose k]_q`. -/
theorem qBinomial_succ_succ' :
    qBinomial q (n + 1) (k + 1) = qBinomial q n (k + 1) + q ^ (n - k) * qBinomial q n k := by
  induction n generalizing k with
  | zero => simp [qBinomial_succ_succ]
  | succ n ih =>
    cases k with
    | zero => simp [qNat_succ]
    | succ k =>
      rcases Nat.lt_or_ge k n with h | h
      · have e1 : n + 1 - (k + 1) = n - k := by omega
        have e2 : n - (k + 1) = n - k - 1 := by omega
        have e3 : k + 1 + 1 + (n - k - 1) = n + 1 := by omega
        have e4 : n - k + (k + 1) = n + 1 := by omega
        have hL : qBinomial q (n + 1 + 1) (k + 1 + 1)
            = qBinomial q n (k + 1) + q ^ (n - k) * qBinomial q n k
              + q ^ (k + 1 + 1) * qBinomial q n (k + 1 + 1)
              + q ^ (n + 1) * qBinomial q n (k + 1) := by
          rw [qBinomial_succ_succ q (n + 1) (k + 1), ih k, ih (k + 1), e2, mul_add, ← mul_assoc,
            ← pow_add, e3]
          abel
        have hR : qBinomial q (n + 1) (k + 1 + 1)
              + q ^ (n + 1 - (k + 1)) * qBinomial q (n + 1) (k + 1)
            = qBinomial q n (k + 1) + q ^ (n - k) * qBinomial q n k
              + q ^ (k + 1 + 1) * qBinomial q n (k + 1 + 1)
              + q ^ (n + 1) * qBinomial q n (k + 1) := by
          rw [e1, qBinomial_succ_succ q n (k + 1), qBinomial_succ_succ q n k, mul_add,
            ← mul_assoc, ← pow_add, e4]
          abel
        rw [hL, hR]
      · rcases eq_or_lt_of_le h with rfl | h'
        · simp [qBinomial_eq_zero_of_lt q (show n + 1 < n + 1 + 1 by omega)]
        · simp [qBinomial_succ_succ q (n + 1) (k + 1), show n - k = 0 by omega,
            qBinomial_eq_zero_of_lt q (show n + 1 < k + 1 + 1 by omega)]

/-- The symmetry `[n choose n - k]_q = [n choose k]_q` of the `q`-binomial coefficients. -/
theorem qBinomial_symm (h : k ≤ n) : qBinomial q n (n - k) = qBinomial q n k := by
  induction n generalizing k with
  | zero => simp_all
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases eq_or_lt_of_le (show k ≤ n by omega) with rfl | h'
      · simp
      · rw [show n + 1 - (k + 1) = n - (k + 1) + 1 by omega, qBinomial_succ_succ,
          ih (k + 1) (by omega), show n - (k + 1) + 1 = n - k by omega, ih k (by omega),
          qBinomial_succ_succ' q n k]

/-- At `q = 1` the `q`-binomial coefficient is the usual binomial coefficient. -/
@[simp] theorem qBinomial_one_left : qBinomial (1 : R) n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih => cases k <;> simp [qBinomial_succ_succ, ih, Nat.choose_succ_succ']

/-- The fundamental relation between two neighbouring `q`-binomial coefficients:
`[n choose k]_q [n - k]_q = [n choose k + 1]_q [k + 1]_q`. -/
theorem qBinomial_mul_qNat_sub :
    qBinomial q n k * qNat q (n - k) = qBinomial q n (k + 1) * qNat q (k + 1) := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases Nat.lt_or_ge k n with h | h
      · have ih1 := ih k
        have ih2 := ih (k + 1)
        have e1 : qNat q (k + 1) + q ^ (k + 1) * qNat q (n - k) = qNat q (n + 1) := by
          rw [← qNat_add]; congr 1; omega
        have e2 : qNat q (k + 1 + 1) + q ^ (k + 1 + 1) * qNat q (n - (k + 1))
            = qNat q (n + 1) := by rw [← qNat_add]; congr 1; omega
        have c1 := (qBinomial_commute_pow q (k + 1) n (k + 1)).eq
        have c2 := (qBinomial_commute_pow q (k + 1 + 1) n (k + 1)).eq
        rw [show n + 1 - (k + 1) = n - k by omega, qBinomial_succ_succ, qBinomial_succ_succ]
        calc (qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)) * qNat q (n - k)
            = qBinomial q n k * qNat q (n - k)
              + q ^ (k + 1) * (qBinomial q n (k + 1) * qNat q (n - k)) := by
                rw [add_mul, mul_assoc]
          _ = qBinomial q n (k + 1) * qNat q (k + 1)
              + qBinomial q n (k + 1) * (q ^ (k + 1) * qNat q (n - k)) := by
                rw [ih1, ← mul_assoc, c1, mul_assoc]
          _ = qBinomial q n (k + 1) * qNat q (n + 1) := by rw [← mul_add, e1]
          _ = qBinomial q n (k + 1) * qNat q (k + 1 + 1)
              + q ^ (k + 1 + 1) * (qBinomial q n (k + 1) * qNat q (n - (k + 1))) := by
                rw [← e2, mul_add, ← mul_assoc, ← c2, mul_assoc]
          _ = (qBinomial q n (k + 1) + q ^ (k + 1 + 1) * qBinomial q n (k + 1 + 1))
              * qNat q (k + 1 + 1) := by rw [ih2, add_mul, mul_assoc]
      · rw [show n + 1 - (k + 1) = 0 by omega, qNat_zero, mul_zero,
          qBinomial_eq_zero_of_lt q (show n + 1 < k + 1 + 1 by omega), zero_mul]

/-- The `q`-analogue of `Nat.choose_mul_factorial_mul_factorial`:
`[n choose k]_q [k]_q ! [n - k]_q ! = [n]_q !`. -/
theorem qBinomial_mul_qFactorial_mul_qFactorial (h : k ≤ n) :
    qBinomial q n k * (qFactorial q k * qFactorial q (n - k)) = qFactorial q n := by
  induction n generalizing k with
  | zero => simp_all
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk : k ≤ n := by omega
      have ih1 := ih k hk
      have hn : qNat q (k + 1) + q ^ (k + 1) * qNat q (n - k) = qNat q (n + 1) := by
        rw [← qNat_add]; congr 1; omega
      rw [show n + 1 - (k + 1) = n - k by omega, qBinomial_succ_succ, qFactorial_succ q k]
      rcases eq_or_lt_of_le hk with rfl | h'
      · rw [qBinomial_eq_zero_of_lt q (Nat.lt_succ_self k), Nat.sub_self, qFactorial_zero,
          qBinomial_self, qFactorial_succ q k, mul_zero, add_zero, mul_one, one_mul]
      · have ih2 := ih (k + 1) (by omega)
        rw [qFactorial_succ q k] at ih2
        rw [show n - k = n - (k + 1) + 1 by omega, qFactorial_succ,
          show n - (k + 1) + 1 = n - k by omega] at ih1 ⊢
        -- abbreviations for the elements involved, all of which commute with each other
        set B₀ := qBinomial q n k
        set B₁ := qBinomial q n (k + 1)
        set F := qFactorial q k
        set G := qFactorial q (n - (k + 1))
        set N := qNat q (k + 1)
        set M := qNat q (n - k)
        have cB₀N : Commute B₀ N := (qNat_commute_qBinomial q (k + 1) n k).symm
        have cB₁M : Commute B₁ M := (qNat_commute_qBinomial q (n - k) n (k + 1)).symm
        have cFM : Commute F M := (qNat_commute_qFactorial q (n - k) k).symm
        have cNM : Commute N M := qNat_commute_qNat q (k + 1) (n - k)
        have t1 : B₀ * (N * F * (M * G)) = N * qFactorial q n := by
          rw [mul_assoc N, cB₀N.left_comm, ih1]
        have t2 : B₁ * (N * F * (M * G)) = M * qFactorial q n := by
          rw [← mul_assoc (N * F), (cNM.mul_left cFM).eq, mul_assoc M, cB₁M.left_comm, ih2]
        calc (B₀ + q ^ (k + 1) * B₁) * (N * F * (M * G))
            = B₀ * (N * F * (M * G)) + q ^ (k + 1) * (B₁ * (N * F * (M * G))) := by
              rw [add_mul, mul_assoc (q ^ (k + 1)) B₁]
          _ = N * qFactorial q n + q ^ (k + 1) * (M * qFactorial q n) := by rw [t1, t2]
          _ = (N + q ^ (k + 1) * M) * qFactorial q n := by rw [add_mul, mul_assoc]
          _ = qFactorial q (n + 1) := by rw [hn, qFactorial_succ]

end Semiring

section Hom

/-- `q`-binomial coefficients commute with (semi)ring homomorphisms. -/
@[simp] theorem map_qBinomial {F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (q : R) (n k : ℕ) :
    f (qBinomial q n k) = qBinomial (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih => cases k <;> simp [qBinomial_succ_succ, ih]

end Hom

/-! ### The `q`-binomial theorem -/

section Semiring
variable [Semiring R]

/-- **The `q`-binomial theorem** (Rothe's formula) for commuting elements `q` and `x`:
`(1 + x) (1 + qx) ⋯ (1 + q ^ (n - 1) x) = ∑_{k ≤ n} q ^ (k choose 2) [n choose k]_q x ^ k`.
The factors of the product on the left commute with each other, so the order is irrelevant;
see `prod_one_add_pow_mul_eq_sum_qBinomial` for the formulation over a commutative semiring. -/
theorem Commute.list_prod_one_add_pow_mul {q x : R} (h : Commute q x) (n : ℕ) :
    ((List.range n).map fun i => 1 + q ^ i * x).prod
      = ∑ k ∈ range (n + 1), q ^ (k.choose 2) * qBinomial q n k * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∀ k ∈ range (n + 1),
        q ^ ((k + 1).choose 2) * qBinomial q (n + 1) (k + 1) * x ^ (k + 1)
          = q ^ ((k + 1).choose 2) * qBinomial q n (k + 1) * x ^ (k + 1)
            + q ^ (k.choose 2) * qBinomial q n k * x ^ k * (q ^ n * x) := by
      intro k hk
      have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using mem_range.mp hk
      have hc : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
      have he : k.choose 2 + k + (n - k) = k.choose 2 + n := by omega
      have hx : x ^ k * q ^ n = q ^ n * x ^ k := (h.symm.pow_pow k n).eq
      have hB : qBinomial q n k * q ^ n = q ^ n * qBinomial q n k :=
        (qBinomial_commute_pow q n n k).eq.symm
      have hterm : q ^ (k.choose 2) * qBinomial q n k * x ^ k * (q ^ n * x)
          = q ^ ((k + 1).choose 2) * (q ^ (n - k) * qBinomial q n k) * x ^ (k + 1) := by
        calc q ^ (k.choose 2) * qBinomial q n k * x ^ k * (q ^ n * x)
            = q ^ (k.choose 2) * qBinomial q n k * (x ^ k * q ^ n) * x := by
              simp only [mul_assoc]
          _ = q ^ (k.choose 2) * qBinomial q n k * (q ^ n * x ^ k) * x := by rw [hx]
          _ = q ^ (k.choose 2) * (qBinomial q n k * q ^ n) * x ^ (k + 1) := by
              simp only [mul_assoc]; rw [← pow_succ]
          _ = q ^ (k.choose 2) * (q ^ n * qBinomial q n k) * x ^ (k + 1) := by rw [hB]
          _ = q ^ (k.choose 2 + n) * qBinomial q n k * x ^ (k + 1) := by
              rw [← mul_assoc, ← pow_add]
          _ = q ^ ((k + 1).choose 2) * (q ^ (n - k) * qBinomial q n k) * x ^ (k + 1) := by
              rw [hc, ← mul_assoc, ← pow_add, he]
      rw [qBinomial_succ_succ' q n k, mul_add, add_mul, hterm]
    have hsplit : ∑ k ∈ range (n + 1), q ^ (k.choose 2) * qBinomial q n k * x ^ k
        = 1 + ∑ k ∈ range (n + 1), q ^ ((k + 1).choose 2) * qBinomial q n (k + 1) * x ^ (k + 1) := by
      rw [sum_range_succ (fun k => q ^ ((k + 1).choose 2) * qBinomial q n (k + 1) * x ^ (k + 1)) n,
        qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n), mul_zero, zero_mul, add_zero,
        sum_range_succ' (fun k => q ^ (k.choose 2) * qBinomial q n k * x ^ k) n]
      simp [add_comm]
    rw [List.prod_range_succ, ih, sum_range_succ' (fun k =>
      q ^ (k.choose 2) * qBinomial q (n + 1) k * x ^ k) (n + 1), sum_congr rfl key,
      sum_add_distrib, mul_add, mul_one, sum_mul, hsplit]
    simp only [Nat.choose_zero_succ, pow_zero, qBinomial_zero_right, mul_one]
    abel

end Semiring

section CommSemiring
variable [CommSemiring R]

/-- **The `q`-binomial theorem** (Rothe's formula) over a commutative semiring:
`∏_{i < n} (1 + q ^ i x) = ∑_{k ≤ n} q ^ (k choose 2) [n choose k]_q x ^ k`. -/
theorem prod_one_add_pow_mul_eq_sum_qBinomial (q x : R) (n : ℕ) :
    ∏ i ∈ range n, (1 + q ^ i * x)
      = ∑ k ∈ range (n + 1), q ^ (k.choose 2) * qBinomial q n k * x ^ k :=
  (Commute.all q x).list_prod_one_add_pow_mul n

end CommSemiring

section Ring
variable [Ring R]

/-- **The `q`-binomial theorem**, in terms of the `q`-Pochhammer symbol:
`(x; q)_n = ∑_{k ≤ n} (-1) ^ k q ^ (k choose 2) [n choose k]_q x ^ k`. -/
theorem Commute.qPochhammer_eq_sum_qBinomial {q x : R} (h : Commute q x) (n : ℕ) :
    qPochhammer q x n
      = ∑ k ∈ range (n + 1), (-1) ^ k * q ^ (k.choose 2) * qBinomial q n k * x ^ k := by
  have hx : Commute q (-x) := h.neg_right
  have hpoch : qPochhammer q x n = ((List.range n).map fun i => 1 + q ^ i * (-x)).prod := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [qPochhammer_succ, ih, List.prod_range_succ, mul_neg, ← sub_eq_add_neg,
        (h.pow_left n).eq]
  rw [hpoch, hx.list_prod_one_add_pow_mul n]
  refine sum_congr rfl fun k _ => ?_
  have hz : Commute ((-1 : R) ^ k) (q ^ (k.choose 2) * qBinomial q n k) :=
    (Commute.neg_one_left _).pow_left k
  rw [neg_pow, ← mul_assoc, ← hz.eq, ← mul_assoc]

end Ring

section CommRing
variable [CommRing R]

/-- **The `q`-binomial theorem** over a commutative ring, in terms of the `q`-Pochhammer symbol:
`(x; q)_n = ∑_{k ≤ n} (-1) ^ k q ^ (k choose 2) [n choose k]_q x ^ k`. -/
theorem qPochhammer_eq_sum_qBinomial (q x : R) (n : ℕ) :
    qPochhammer q x n
      = ∑ k ∈ range (n + 1), (-1) ^ k * q ^ (k.choose 2) * qBinomial q n k * x ^ k :=
  (Commute.all q x).qPochhammer_eq_sum_qBinomial n

end CommRing

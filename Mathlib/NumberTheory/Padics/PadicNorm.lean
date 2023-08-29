/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Algebra.Order.Field.Power
import Mathlib.NumberTheory.Padics.PadicVal

#align_import number_theory.padics.padic_norm from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/


/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)
#align padic_norm padicNorm

namespace padicNorm

open padicValRat

variable {p : ℕ}

/-- Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`. -/
@[simp]
protected theorem eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
    padicNorm p q = (p : ℚ) ^ (-padicValRat p q) := by simp [hq, padicNorm]
                                                       -- 🎉 no goals
#align padic_norm.eq_zpow_of_nonzero padicNorm.eq_zpow_of_nonzero

/-- The `p`-adic norm is nonnegative. -/
protected theorem nonneg (q : ℚ) : 0 ≤ padicNorm p q :=
  if hq : q = 0 then by simp [hq, padicNorm]
                        -- 🎉 no goals
  else by
    unfold padicNorm
    -- ⊢ 0 ≤ if q = 0 then 0 else ↑p ^ (-padicValRat p q)
    split_ifs
    -- ⊢ 0 ≤ ↑p ^ (-padicValRat p q)
    apply zpow_nonneg
    -- ⊢ 0 ≤ ↑p
    exact_mod_cast Nat.zero_le _
    -- 🎉 no goals
#align padic_norm.nonneg padicNorm.nonneg

/-- The `p`-adic norm of `0` is `0`. -/
@[simp]
protected theorem zero : padicNorm p 0 = 0 := by simp [padicNorm]
                                                 -- 🎉 no goals
#align padic_norm.zero padicNorm.zero

/-- The `p`-adic norm of `1` is `1`. -/
-- @[simp] -- Porting note: simp can prove this
protected theorem one : padicNorm p 1 = 1 := by simp [padicNorm]
                                                -- 🎉 no goals
#align padic_norm.one padicNorm.one

/-- The `p`-adic norm of `p` is `p⁻¹` if `p > 1`.

See also `padicNorm.padicNorm_p_of_prime` for a version assuming `p` is prime. -/
theorem padicNorm_p (hp : 1 < p) : padicNorm p p = (p : ℚ)⁻¹ := by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]
  -- 🎉 no goals
#align padic_norm.padic_norm_p padicNorm.padicNorm_p

/-- The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padicNorm.padicNorm_p` for a version assuming `1 < p`. -/
@[simp]
theorem padicNorm_p_of_prime [Fact p.Prime] : padicNorm p p = (p : ℚ)⁻¹ :=
  padicNorm_p <| Nat.Prime.one_lt Fact.out
#align padic_norm.padic_norm_p_of_prime padicNorm.padicNorm_p_of_prime

/-- The `p`-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
theorem padicNorm_of_prime_of_ne {q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
    (neq : p ≠ q) : padicNorm p q = 1 := by
  have p : padicValRat p q = 0 := by exact_mod_cast padicValNat_primes neq
  -- ⊢ padicNorm p✝ ↑q = 1
  rw [padicNorm, p]
  -- ⊢ (if ↑q = 0 then 0 else ↑p✝ ^ (-0)) = 1
  simp [q_prime.1.ne_zero]
  -- 🎉 no goals
#align padic_norm.padic_norm_of_prime_of_ne padicNorm.padicNorm_of_prime_of_ne

/-- The `p`-adic norm of `p` is less than `1` if `1 < p`.

See also `padicNorm.padicNorm_p_lt_one_of_prime` for a version assuming `p` is prime. -/
theorem padicNorm_p_lt_one (hp : 1 < p) : padicNorm p p < 1 := by
  rw [padicNorm_p hp, inv_lt_one_iff]
  -- ⊢ ↑p ≤ 0 ∨ 1 < ↑p
  exact_mod_cast Or.inr hp
  -- 🎉 no goals
#align padic_norm.padic_norm_p_lt_one padicNorm.padicNorm_p_lt_one

/-- The `p`-adic norm of `p` is less than `1` if `p` is prime.

See also `padicNorm.padicNorm_p_lt_one` for a version assuming `1 < p`. -/
theorem padicNorm_p_lt_one_of_prime [Fact p.Prime] : padicNorm p p < 1 :=
  padicNorm_p_lt_one <| Nat.Prime.one_lt Fact.out
#align padic_norm.padic_norm_p_lt_one_of_prime padicNorm.padicNorm_p_lt_one_of_prime

/-- `padicNorm p q` takes discrete values `p ^ -z` for `z : ℤ`. -/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padicNorm p q = (p : ℚ) ^ (-z) :=
  ⟨padicValRat p q, by simp [padicNorm, hq]⟩
                       -- 🎉 no goals
#align padic_norm.values_discrete padicNorm.values_discrete

/-- `padicNorm p` is symmetric. -/
@[simp]
protected theorem neg (q : ℚ) : padicNorm p (-q) = padicNorm p q :=
  if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]
                        -- 🎉 no goals
                                          -- 🎉 no goals
#align padic_norm.neg padicNorm.neg

variable [hp : Fact p.Prime]

/-- If `q ≠ 0`, then `padicNorm p q ≠ 0`. -/
protected theorem nonzero {q : ℚ} (hq : q ≠ 0) : padicNorm p q ≠ 0 := by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  -- ⊢ ↑p ^ (-padicValRat p q) ≠ 0
  apply zpow_ne_zero_of_ne_zero
  -- ⊢ ↑p ≠ 0
  exact_mod_cast ne_of_gt hp.1.pos
  -- 🎉 no goals
#align padic_norm.nonzero padicNorm.nonzero

/-- If the `p`-adic norm of `q` is 0, then `q` is `0`. -/
theorem zero_of_padicNorm_eq_zero {q : ℚ} (h : padicNorm p q = 0) : q = 0 := by
  apply by_contradiction; intro hq
  -- ⊢ ¬q = 0 → False
                          -- ⊢ False
  unfold padicNorm at h; rw [if_neg hq] at h
  -- ⊢ False
                         -- ⊢ False
  apply absurd h
  -- ⊢ ¬↑p ^ (-padicValRat p q) = 0
  apply zpow_ne_zero_of_ne_zero
  -- ⊢ ↑p ≠ 0
  exact_mod_cast hp.1.ne_zero
  -- 🎉 no goals
#align padic_norm.zero_of_padic_norm_eq_zero padicNorm.zero_of_padicNorm_eq_zero

/-- The `p`-adic norm is multiplicative. -/
@[simp]
protected theorem mul (q r : ℚ) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
  if hq : q = 0 then by simp [hq]
                        -- 🎉 no goals
  else
    if hr : r = 0 then by simp [hr]
                          -- 🎉 no goals
    else by
      have : (p : ℚ) ≠ 0 := by simp [hp.1.ne_zero]
      -- ⊢ padicNorm p (q * r) = padicNorm p q * padicNorm p r
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]
      -- 🎉 no goals
#align padic_norm.mul padicNorm.mul

/-- The `p`-adic norm respects division. -/
@[simp]
protected theorem div (q r : ℚ) : padicNorm p (q / r) = padicNorm p q / padicNorm p r :=
  if hr : r = 0 then by simp [hr]
                        -- 🎉 no goals
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel _ hr])
                                                   -- 🎉 no goals
#align padic_norm.div padicNorm.div

/-- The `p`-adic norm of an integer is at most `1`. -/
protected theorem of_int (z : ℤ) : padicNorm p z ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
                        -- 🎉 no goals
  else by
    unfold padicNorm
    -- ⊢ (if ↑z = 0 then 0 else ↑p ^ (-padicValRat p ↑z)) ≤ 1
    rw [if_neg _]
    -- ⊢ ↑p ^ (-padicValRat p ↑z) ≤ 1
    · refine' zpow_le_one_of_nonpos _ _
      -- ⊢ 1 ≤ ↑p
      · exact_mod_cast le_of_lt hp.1.one_lt
        -- 🎉 no goals
      · rw [padicValRat.of_int, neg_nonpos]
        -- ⊢ 0 ≤ ↑(padicValInt p z)
        norm_cast
        -- ⊢ 0 ≤ padicValInt p z
        simp
        -- 🎉 no goals
    exact_mod_cast hz
    -- 🎉 no goals
#align padic_norm.of_int padicNorm.of_int

private theorem nonarchimedean_aux {q r : ℚ} (h : padicValRat p q ≤ padicValRat p r) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  have hnqp : padicNorm p q ≥ 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r ≥ 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp, le_max_right]
                        -- 🎉 no goals
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp, le_max_left]
                          -- 🎉 no goals
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
                                           -- 🎉 no goals
      else by
        unfold padicNorm; split_ifs
        -- ⊢ (if q + r = 0 then 0 else ↑p ^ (-padicValRat p (q + r))) ≤ max (if q = 0 the …
                          -- ⊢ ↑p ^ (-padicValRat p (q + r)) ≤ max (↑p ^ (-padicValRat p q)) (↑p ^ (-padicV …
        apply le_max_iff.2
        -- ⊢ ↑p ^ (-padicValRat p (q + r)) ≤ ↑p ^ (-padicValRat p q) ∨ ↑p ^ (-padicValRat …
        left
        -- ⊢ ↑p ^ (-padicValRat p (q + r)) ≤ ↑p ^ (-padicValRat p q)
        apply zpow_le_of_le
        -- ⊢ 1 ≤ ↑p
        · exact_mod_cast le_of_lt hp.1.one_lt
          -- 🎉 no goals
        · apply neg_le_neg
          -- ⊢ padicValRat p q ≤ padicValRat p (q + r)
          have : padicValRat p q = min (padicValRat p q) (padicValRat p r) := (min_eq_left h).symm
          -- ⊢ padicValRat p q ≤ padicValRat p (q + r)
          rw [this]
          -- ⊢ min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r)
          exact min_le_padicValRat_add hqr
          -- 🎉 no goals

/-- The `p`-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p`
and the norm of `q`. -/
protected theorem nonarchimedean {q r : ℚ} :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := by
  wlog hle : padicValRat p q ≤ padicValRat p r generalizing q r
  -- ⊢ padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)
  · rw [add_comm, max_comm]
    -- ⊢ padicNorm p (r + q) ≤ max (padicNorm p r) (padicNorm p q)
    exact this (le_of_not_le hle)
    -- 🎉 no goals
  exact nonarchimedean_aux hle
  -- 🎉 no goals
#align padic_norm.nonarchimedean padicNorm.nonarchimedean

/-- The `p`-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of
`p` plus the norm of `q`. -/
theorem triangle_ineq (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q + padicNorm p r :=
  calc
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ ≤ padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
#align padic_norm.triangle_ineq padicNorm.triangle_ineq

/-- The `p`-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the `p`-adic norm. -/
protected theorem sub {q r : ℚ} : padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) := by
  rw [sub_eq_add_neg, ← padicNorm.neg r]
  -- ⊢ padicNorm p (q + -r) ≤ max (padicNorm p q) (padicNorm p (-r))
  exact padicNorm.nonarchimedean
  -- 🎉 no goals
#align padic_norm.sub padicNorm.sub

/-- If the `p`-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max
of the norms of `q` and `r`. -/
theorem add_eq_max_of_ne {q r : ℚ} (hne : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) := by
  wlog hlt : padicNorm p r < padicNorm p q
  -- ⊢ padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r)
  · rw [add_comm, max_comm]
    -- ⊢ padicNorm p (r + q) = max (padicNorm p r) (padicNorm p q)
    exact this hne.symm (hne.lt_or_lt.resolve_right hlt)
    -- 🎉 no goals
  have : padicNorm p q ≤ max (padicNorm p (q + r)) (padicNorm p r) :=
    calc
      padicNorm p q = padicNorm p (q + r + (-r)) := by ring_nf
      _ ≤ max (padicNorm p (q + r)) (padicNorm p (-r)) := padicNorm.nonarchimedean
      _ = max (padicNorm p (q + r)) (padicNorm p r) := by simp
  have hnge : padicNorm p r ≤ padicNorm p (q + r) := by
    apply le_of_not_gt
    intro hgt
    rw [max_eq_right_of_lt hgt] at this
    exact not_lt_of_ge this hlt
  have : padicNorm p q ≤ padicNorm p (q + r) := by rwa [max_eq_left hnge] at this
  -- ⊢ padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r)
  apply _root_.le_antisymm
  -- ⊢ padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)
  · apply padicNorm.nonarchimedean
    -- 🎉 no goals
  · rwa [max_eq_left_of_lt hlt]
    -- 🎉 no goals
#align padic_norm.add_eq_max_of_ne padicNorm.add_eq_max_of_ne

/-- The `p`-adic norm is an absolute value: positive-definite and multiplicative, satisfying the
triangle inequality. -/
instance : IsAbsoluteValue (padicNorm p)
    where
  abv_nonneg' := padicNorm.nonneg
  abv_eq_zero' := ⟨zero_of_padicNorm_eq_zero, fun hx ↦ by simp [hx]⟩
                                                          -- 🎉 no goals
  abv_add' := padicNorm.triangle_ineq
  abv_mul' := padicNorm.mul

theorem dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padicNorm p z ≤ (p : ℚ) ^ (-n : ℤ) := by
  unfold padicNorm; split_ifs with hz
  -- ⊢ ↑(p ^ n) ∣ z ↔ (if ↑z = 0 then 0 else ↑p ^ (-padicValRat p ↑z)) ≤ ↑p ^ (-↑n)
                    -- ⊢ ↑(p ^ n) ∣ z ↔ 0 ≤ ↑p ^ (-↑n)
  · norm_cast at hz
    -- ⊢ ↑(p ^ n) ∣ z ↔ 0 ≤ ↑p ^ (-↑n)
    simp [hz]
    -- 🎉 no goals
  · rw [zpow_le_iff_le, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      -- ⊢ ↑(p ^ n) ∣ z ↔ n ≤ Part.get (multiplicity (↑p) z) (_ : multiplicity.Finite ( …
      rw [← PartENat.coe_le_coe, PartENat.natCast_get, ← multiplicity.pow_dvd_iff_le_multiplicity,
        Nat.cast_pow]
      exact_mod_cast hz
      -- 🎉 no goals
    · exact_mod_cast hp.1.one_lt
      -- 🎉 no goals
#align padic_norm.dvd_iff_norm_le padicNorm.dvd_iff_norm_le

/-- The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`. -/
theorem int_eq_one_iff (m : ℤ) : padicNorm p m = 1 ↔ ¬(p : ℤ) ∣ m := by
  nth_rw 2 [← pow_one p]
  -- ⊢ padicNorm p ↑m = 1 ↔ ¬↑(p ^ 1) ∣ m
  simp only [dvd_iff_norm_le, Int.cast_ofNat, Nat.cast_one, zpow_neg, zpow_one, not_le]
  -- ⊢ padicNorm p ↑m = 1 ↔ (↑p)⁻¹ < padicNorm p ↑m
  constructor
  -- ⊢ padicNorm p ↑m = 1 → (↑p)⁻¹ < padicNorm p ↑m
  · intro h
    -- ⊢ (↑p)⁻¹ < padicNorm p ↑m
    rw [h, inv_lt_one_iff_of_pos] <;> norm_cast
    -- ⊢ 1 < ↑p
                                      -- ⊢ 1 < p
                                      -- ⊢ 0 < p
    · exact Nat.Prime.one_lt Fact.out
      -- 🎉 no goals
    · exact Nat.Prime.pos Fact.out
      -- 🎉 no goals
  · simp only [padicNorm]
    -- ⊢ ((↑p)⁻¹ < if ↑m = 0 then 0 else ↑p ^ (-padicValRat p ↑m)) → (if ↑m = 0 then  …
    split_ifs
    -- ⊢ (↑p)⁻¹ < 0 → 0 = 1
    · rw [inv_lt_zero, ← Nat.cast_zero, Nat.cast_lt]
      -- ⊢ p < 0 → ↑0 = 1
      intro h
      -- ⊢ ↑0 = 1
      exact (Nat.not_lt_zero p h).elim
      -- 🎉 no goals
    · have : 1 < (p : ℚ) := by norm_cast; exact Nat.Prime.one_lt (Fact.out : Nat.Prime p)
      -- ⊢ (↑p)⁻¹ < ↑p ^ (-padicValRat p ↑m) → ↑p ^ (-padicValRat p ↑m) = 1
      rw [← zpow_neg_one, zpow_lt_iff_lt this]
      -- ⊢ -1 < -padicValRat p ↑m → ↑p ^ (-padicValRat p ↑m) = 1
      have : 0 ≤ padicValRat p m
      -- ⊢ 0 ≤ padicValRat p ↑m
      simp only [of_int, Nat.cast_nonneg]
      -- ⊢ -1 < -padicValRat p ↑m → ↑p ^ (-padicValRat p ↑m) = 1
      intro h
      -- ⊢ ↑p ^ (-padicValRat p ↑m) = 1
      rw [← zpow_zero (p : ℚ), zpow_inj] <;> linarith
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align padic_norm.int_eq_one_iff padicNorm.int_eq_one_iff

theorem int_lt_one_iff (m : ℤ) : padicNorm p m < 1 ↔ (p : ℤ) ∣ m := by
  rw [← not_iff_not, ← int_eq_one_iff, eq_iff_le_not_lt]
  -- ⊢ ¬padicNorm p ↑m < 1 ↔ padicNorm p ↑m ≤ 1 ∧ ¬padicNorm p ↑m < 1
  simp only [padicNorm.of_int, true_and_iff]
  -- 🎉 no goals
#align padic_norm.int_lt_one_iff padicNorm.int_lt_one_iff

theorem of_nat (m : ℕ) : padicNorm p m ≤ 1 :=
  padicNorm.of_int (m : ℤ)
#align padic_norm.of_nat padicNorm.of_nat

/-- The `p`-adic norm of a natural `m` is one iff `p` doesn't divide `m`. -/
theorem nat_eq_one_iff (m : ℕ) : padicNorm p m = 1 ↔ ¬p ∣ m := by
  rw [← Int.coe_nat_dvd, ← int_eq_one_iff, Int.cast_ofNat]
  -- 🎉 no goals
#align padic_norm.nat_eq_one_iff padicNorm.nat_eq_one_iff

theorem nat_lt_one_iff (m : ℕ) : padicNorm p m < 1 ↔ p ∣ m := by
  rw [← Int.coe_nat_dvd, ← int_lt_one_iff, Int.cast_ofNat]
  -- 🎉 no goals
#align padic_norm.nat_lt_one_iff padicNorm.nat_lt_one_iff

open BigOperators

theorem sum_lt {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α} :
    s.Nonempty → (∀ i ∈ s, padicNorm p (F i) < t) → padicNorm p (∑ i in s, F i) < t := by
  classical
    refine' s.induction_on (by rintro ⟨-, ⟨⟩⟩) _
    rintro a S haS IH - ht
    by_cases hs : S.Nonempty
    · rw [Finset.sum_insert haS]
      exact
        lt_of_le_of_lt padicNorm.nonarchimedean
          (max_lt (ht a (Finset.mem_insert_self a S))
            (IH hs fun b hb ↦ ht b (Finset.mem_insert_of_mem hb)))
    · simp_all
#align padic_norm.sum_lt padicNorm.sum_lt

theorem sum_le {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α} :
    s.Nonempty → (∀ i ∈ s, padicNorm p (F i) ≤ t) → padicNorm p (∑ i in s, F i) ≤ t := by
  classical
    refine' s.induction_on (by rintro ⟨-, ⟨⟩⟩) _
    rintro a S haS IH - ht
    by_cases hs : S.Nonempty
    · rw [Finset.sum_insert haS]
      exact
        padicNorm.nonarchimedean.trans
          (max_le (ht a (Finset.mem_insert_self a S))
            (IH hs fun b hb ↦ ht b (Finset.mem_insert_of_mem hb)))
    · simp_all
#align padic_norm.sum_le padicNorm.sum_le

theorem sum_lt' {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) < t) (ht : 0 < t) : padicNorm p (∑ i in s, F i) < t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  -- ⊢ padicNorm p (∑ i in ∅, F i) < t
  · simp [ht]
    -- 🎉 no goals
  · exact sum_lt hs hF
    -- 🎉 no goals
#align padic_norm.sum_lt' padicNorm.sum_lt'

theorem sum_le' {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) ≤ t) (ht : 0 ≤ t) : padicNorm p (∑ i in s, F i) ≤ t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  -- ⊢ padicNorm p (∑ i in ∅, F i) ≤ t
  · simp [ht]
    -- 🎉 no goals
  · exact sum_le hs hF
    -- 🎉 no goals
#align padic_norm.sum_le' padicNorm.sum_le'

end padicNorm

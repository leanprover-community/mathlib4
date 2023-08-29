/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Polynomial.RingDivision

#align_import data.polynomial.mirror from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# "Mirror" of a univariate polynomial

In this file we define `Polynomial.mirror`, a variant of `Polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `Polynomial.mirror`

## Main results

- `Polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `Polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/


namespace Polynomial

open Polynomial

section Semiring

variable {R : Type*} [Semiring R] (p q : R[X])

/-- mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree` -/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree
#align polynomial.mirror Polynomial.mirror

@[simp]
theorem mirror_zero : (0 : R[X]).mirror = 0 := by simp [mirror]
                                                  -- 🎉 no goals
#align polynomial.mirror_zero Polynomial.mirror_zero

theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]
#align polynomial.mirror_monomial Polynomial.mirror_monomial

theorem mirror_C (a : R) : (C a).mirror = C a :=
  mirror_monomial 0 a
set_option linter.uppercaseLean3 false in
#align polynomial.mirror_C Polynomial.mirror_C

theorem mirror_X : X.mirror = (X : R[X]) :=
  mirror_monomial 1 (1 : R)
set_option linter.uppercaseLean3 false in
#align polynomial.mirror_X Polynomial.mirror_X

theorem mirror_natDegree : p.mirror.natDegree = p.natDegree := by
  by_cases hp : p = 0
  -- ⊢ natDegree (mirror p) = natDegree p
  · rw [hp, mirror_zero]
    -- 🎉 no goals
  nontriviality R
  -- ⊢ natDegree (mirror p) = natDegree p
  rw [mirror, natDegree_mul', reverse_natDegree, natDegree_X_pow,
    tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]
  -- 🎉 no goals
#align polynomial.mirror_nat_degree Polynomial.mirror_natDegree

theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  -- ⊢ natTrailingDegree (mirror p) = natTrailingDegree p
  · rw [hp, mirror_zero]
    -- 🎉 no goals
  · rw [mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      reverse_natTrailingDegree, zero_add]
#align polynomial.mirror_nat_trailing_degree Polynomial.mirror_natTrailingDegree

theorem coeff_mirror (n : ℕ) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by
  by_cases h2 : p.natDegree < n
  -- ⊢ coeff (mirror p) n = coeff p (↑(revAt (natDegree p + natTrailingDegree p)) n)
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [mirror_natDegree])]
    -- ⊢ 0 = coeff p (↑(revAt (natDegree p + natTrailingDegree p)) n)
    by_cases h1 : n ≤ p.natDegree + p.natTrailingDegree
    -- ⊢ 0 = coeff p (↑(revAt (natDegree p + natTrailingDegree p)) n)
    · rw [revAt_le h1, coeff_eq_zero_of_lt_natTrailingDegree]
      -- ⊢ natDegree p + natTrailingDegree p - n < natTrailingDegree p
      exact (tsub_lt_iff_left h1).mpr (Nat.add_lt_add_right h2 _)
      -- 🎉 no goals
    · rw [← revAtFun_eq, revAtFun, if_neg h1, coeff_eq_zero_of_natDegree_lt h2]
      -- 🎉 no goals
  rw [not_lt] at h2
  -- ⊢ coeff (mirror p) n = coeff p (↑(revAt (natDegree p + natTrailingDegree p)) n)
  rw [revAt_le (h2.trans (Nat.le_add_right _ _))]
  -- ⊢ coeff (mirror p) n = coeff p (natDegree p + natTrailingDegree p - n)
  by_cases h3 : p.natTrailingDegree ≤ n
  -- ⊢ coeff (mirror p) n = coeff p (natDegree p + natTrailingDegree p - n)
  · rw [← tsub_add_eq_add_tsub h2, ← tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow', if_pos h3,
      coeff_reverse, revAt_le (tsub_le_self.trans h2)]
  rw [not_le] at h3
  -- ⊢ coeff (mirror p) n = coeff p (natDegree p + natTrailingDegree p - n)
  rw [coeff_eq_zero_of_natDegree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_left h3 _))]
  -- ⊢ coeff (mirror p) n = 0
  exact coeff_eq_zero_of_lt_natTrailingDegree (by rwa [mirror_natTrailingDegree])
  -- 🎉 no goals
#align polynomial.coeff_mirror Polynomial.coeff_mirror

--TODO: Extract `Finset.sum_range_rev_at` lemma.
theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, mirror_natDegree]
  -- ⊢ (Finset.sum (Finset.range (natDegree p + 1)) fun x => coeff (mirror p) x) =  …
  refine' Finset.sum_bij_ne_zero _ _ _ _ _
  · exact fun n _ _ => revAt (p.natDegree + p.natTrailingDegree) n
    -- 🎉 no goals
  · intro n hn hp
    -- ⊢ ↑(revAt (natDegree p + natTrailingDegree p)) n ∈ Finset.range (natDegree p + …
    rw [Finset.mem_range_succ_iff] at *
    -- ⊢ ↑(revAt (natDegree p + natTrailingDegree p)) n ≤ natDegree p
    rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
    -- ⊢ natDegree p + natTrailingDegree p - n ≤ natDegree p
    rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right, ← mirror_natTrailingDegree]
    -- ⊢ natTrailingDegree (mirror p) ≤ n
    exact natTrailingDegree_le_of_ne_zero hp
    -- 🎉 no goals
  · exact fun n₁ n₂ _ _ _ _ h => by rw [← @revAt_invol _ n₁, h, revAt_invol]
    -- 🎉 no goals
  · intro n hn hp
    -- ⊢ ∃ a h₁ h₂, n = ↑(revAt (natDegree p + natTrailingDegree p)) a
    use revAt (p.natDegree + p.natTrailingDegree) n
    -- ⊢ ∃ h₁ h₂, n = ↑(revAt (natDegree p + natTrailingDegree p)) (↑(revAt (natDegre …
    refine' ⟨_, _, revAt_invol.symm⟩
    -- ⊢ ↑(revAt (natDegree p + natTrailingDegree p)) n ∈ Finset.range (natDegree p + …
    · rw [Finset.mem_range_succ_iff] at *
      -- ⊢ ↑(revAt (natDegree p + natTrailingDegree p)) n ≤ natDegree p
      rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
      -- ⊢ natDegree p + natTrailingDegree p - n ≤ natDegree p
      rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right]
      -- ⊢ natTrailingDegree p ≤ n
      exact natTrailingDegree_le_of_ne_zero hp
      -- 🎉 no goals
    · change p.mirror.coeff _ ≠ 0
      -- ⊢ coeff (mirror p) (↑(revAt (natDegree p + natTrailingDegree p)) n) ≠ 0
      rwa [coeff_mirror, revAt_invol]
      -- 🎉 no goals
  · exact fun n _ _ => p.coeff_mirror n
    -- 🎉 no goals
#align polynomial.mirror_eval_one Polynomial.mirror_eval_one

theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext fun n => by
    rw [coeff_mirror, coeff_mirror, mirror_natDegree, mirror_natTrailingDegree, revAt_invol]
    -- 🎉 no goals
#align polynomial.mirror_mirror Polynomial.mirror_mirror

variable {p q}

theorem mirror_involutive : Function.Involutive (mirror : R[X] → R[X]) :=
  mirror_mirror
#align polynomial.mirror_involutive Polynomial.mirror_involutive

theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
  mirror_involutive.eq_iff
#align polynomial.mirror_eq_iff Polynomial.mirror_eq_iff

@[simp]
theorem mirror_inj : p.mirror = q.mirror ↔ p = q :=
  mirror_involutive.injective.eq_iff
#align polynomial.mirror_inj Polynomial.mirror_inj

@[simp]
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩
               -- 🎉 no goals
                                                                   -- 🎉 no goals
#align polynomial.mirror_eq_zero Polynomial.mirror_eq_zero

variable (p q)

@[simp]
theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, trailingCoeff, mirror_natTrailingDegree, coeff_mirror,
    revAt_le (Nat.le_add_left _ _), add_tsub_cancel_right]
#align polynomial.mirror_trailing_coeff Polynomial.mirror_trailingCoeff

@[simp]
theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← p.mirror_mirror, mirror_trailingCoeff, p.mirror_mirror]
  -- 🎉 no goals
#align polynomial.mirror_leading_coeff Polynomial.mirror_leadingCoeff

theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.sum fun n => (· ^ 2) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- ⊢ (Finset.sum (Finset.range (Nat.succ (natDegree p + natTrailingDegree p))) fu …
  refine'
    (Finset.sum_congr rfl fun n hn => _).trans
      (p.sum_eq_of_subset (fun _ => (· ^ 2)) (fun _ => zero_pow zero_lt_two) fun n hn =>
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp n hn).trans (Nat.le_add_right _ _))).symm
  rw [coeff_mirror, ← revAt_le (Finset.mem_range_succ_iff.mp hn), revAt_invol, ← sq]
  -- 🎉 no goals
#align polynomial.coeff_mul_mirror Polynomial.coeff_mul_mirror

variable [NoZeroDivisors R]

theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by
  by_cases hp : p = 0
  -- ⊢ natDegree (p * mirror p) = 2 * natDegree p
  · rw [hp, zero_mul, natDegree_zero, mul_zero]
    -- 🎉 no goals
  rw [natDegree_mul hp (mt mirror_eq_zero.mp hp), mirror_natDegree, two_mul]
  -- 🎉 no goals
#align polynomial.nat_degree_mul_mirror Polynomial.natDegree_mul_mirror

theorem natTrailingDegree_mul_mirror :
    (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by
  by_cases hp : p = 0
  -- ⊢ natTrailingDegree (p * mirror p) = 2 * natTrailingDegree p
  · rw [hp, zero_mul, natTrailingDegree_zero, mul_zero]
    -- 🎉 no goals
  rw [natTrailingDegree_mul hp (mt mirror_eq_zero.mp hp), mirror_natTrailingDegree, two_mul]
  -- 🎉 no goals
#align polynomial.nat_trailing_degree_mul_mirror Polynomial.natTrailingDegree_mul_mirror

end Semiring

section Ring

variable {R : Type*} [Ring R] (p q : R[X])

theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [mirror, mirror, reverse_neg, natTrailingDegree_neg, neg_mul_eq_neg_mul]
  -- 🎉 no goals
#align polynomial.mirror_neg Polynomial.mirror_neg

variable [NoZeroDivisors R]

theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by
  by_cases hp : p = 0
  -- ⊢ mirror (p * q) = mirror p * mirror q
  · rw [hp, zero_mul, mirror_zero, zero_mul]
    -- 🎉 no goals
  by_cases hq : q = 0
  -- ⊢ mirror (p * q) = mirror p * mirror q
  · rw [hq, mul_zero, mirror_zero, mul_zero]
    -- 🎉 no goals
  rw [mirror, mirror, mirror, reverse_mul_of_domain, natTrailingDegree_mul hp hq, pow_add]
  -- ⊢ reverse p * reverse q * (X ^ natTrailingDegree p * X ^ natTrailingDegree q)  …
  rw [mul_assoc, ← mul_assoc q.reverse, ← X_pow_mul (p := reverse q)]
  -- ⊢ reverse p * (X ^ natTrailingDegree p * reverse q * X ^ natTrailingDegree q)  …
  repeat' rw [mul_assoc]
  -- 🎉 no goals
#align polynomial.mirror_mul_of_domain Polynomial.mirror_mul_of_domain

theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  rw [← C_mul', ← C_mul', mirror_mul_of_domain, mirror_C]
  -- 🎉 no goals
#align polynomial.mirror_smul Polynomial.mirror_smul

end Ring

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : ∀ g, g ∣ f → g ∣ f.mirror → IsUnit g) : Irreducible f := by
  constructor
  -- ⊢ ¬IsUnit f
  · exact h1
    -- 🎉 no goals
  · intro g h fgh
    -- ⊢ IsUnit g ∨ IsUnit h
    let k := g * h.mirror
    -- ⊢ IsUnit g ∨ IsUnit h
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror, mul_assoc, mul_comm h,
        mul_comm g.mirror, mul_assoc, ← mul_assoc]
    have g_dvd_f : g ∣ f := by
      rw [fgh]
      exact dvd_mul_right g h
    have h_dvd_f : h ∣ f := by
      rw [fgh]
      exact dvd_mul_left h g
    have g_dvd_k : g ∣ k := dvd_mul_right g h.mirror
    -- ⊢ IsUnit g ∨ IsUnit h
    have h_dvd_k_rev : h ∣ k.mirror := by
      rw [mirror_mul_of_domain, mirror_mirror]
      exact dvd_mul_left h g.mirror
    have hk := h2 k key
    -- ⊢ IsUnit g ∨ IsUnit h
    rcases hk with (hk | hk | hk | hk)
    · exact Or.inr (h3 h h_dvd_f (by rwa [← hk]))
      -- 🎉 no goals
    · exact Or.inr (h3 h h_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, mirror_neg, dvd_neg]))
      -- 🎉 no goals
    · exact Or.inl (h3 g g_dvd_f (by rwa [← hk]))
      -- 🎉 no goals
    · exact Or.inl (h3 g g_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, dvd_neg]))
      -- 🎉 no goals
#align polynomial.irreducible_of_mirror Polynomial.irreducible_of_mirror

end CommRing

end Polynomial

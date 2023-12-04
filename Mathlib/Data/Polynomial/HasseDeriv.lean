/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Tactic.FieldSimp

#align_import data.polynomial.hasse_deriv from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Hasse derivative of polynomials

The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It is a variant of the usual derivative, and satisfies `k! * (hasseDeriv k f) = derivative^[k] f`.
The main benefit is that is gives an atomic way of talking about expressions such as
`(derivative^[k] f).eval r / k!`, that occur in Taylor expansions, for example.

## Main declarations

In the following, we write `D k` for the `k`-th Hasse derivative `hasse_deriv k`.

* `Polynomial.hasseDeriv`: the `k`-th Hasse derivative of a polynomial
* `Polynomial.hasseDeriv_zero`: the `0`th Hasse derivative is the identity
* `Polynomial.hasseDeriv_one`: the `1`st Hasse derivative is the usual derivative
* `Polynomial.factorial_smul_hasseDeriv`: the identity `k! • (D k f) = derivative^[k] f`
* `Polynomial.hasseDeriv_comp`: the identity `(D k).comp (D l) = (k+l).choose k • D (k+l)`
* `Polynomial.hasseDeriv_mul`:
  the "Leibniz rule" `D k (f * g) = ∑ ij in antidiagonal k, D ij.1 f * D ij.2 g`

For the identity principle, see `Polynomial.eq_zero_of_hasseDeriv_eq_zero`
in `Data/Polynomial/Taylor.lean`.

## Reference

https://math.fontein.de/2009/08/12/the-hasse-derivative/

-/


noncomputable section

namespace Polynomial

open Nat BigOperators Polynomial

open Function

open Nat hiding nsmul_eq_mul

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

/-- The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_deriv k f) = derivative^[k] f`. -/
def hasseDeriv (k : ℕ) : R[X] →ₗ[R] R[X] :=
  lsum fun i => monomial (i - k) ∘ₗ DistribMulAction.toLinearMap R R (i.choose k)
#align polynomial.hasse_deriv Polynomial.hasseDeriv

theorem hasseDeriv_apply :
    hasseDeriv k f = f.sum fun i r => monomial (i - k) (↑(i.choose k) * r) := by
  dsimp [hasseDeriv]
  congr; ext; congr
  apply nsmul_eq_mul
#align polynomial.hasse_deriv_apply Polynomial.hasseDeriv_apply

theorem hasseDeriv_coeff (n : ℕ) :
    (hasseDeriv k f).coeff n = (n + k).choose k * f.coeff (n + k) := by
  rw [hasseDeriv_apply, coeff_sum, sum_def, Finset.sum_eq_single (n + k), coeff_monomial]
  · simp only [if_true, add_tsub_cancel_right, eq_self_iff_true]
  · intro i _hi hink
    rw [coeff_monomial]
    by_cases hik : i < k
    · simp only [Nat.choose_eq_zero_of_lt hik, ite_self, Nat.cast_zero, zero_mul]
    · push_neg at hik
      rw [if_neg]
      contrapose! hink
      exact (tsub_eq_iff_eq_add_of_le hik).mp hink
  · intro h
    simp only [not_mem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero]
#align polynomial.hasse_deriv_coeff Polynomial.hasseDeriv_coeff

theorem hasseDeriv_zero' : hasseDeriv 0 f = f := by
  simp only [hasseDeriv_apply, tsub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
    sum_monomial_eq]
#align polynomial.hasse_deriv_zero' Polynomial.hasseDeriv_zero'

@[simp]
theorem hasseDeriv_zero : @hasseDeriv R _ 0 = LinearMap.id :=
  LinearMap.ext <| hasseDeriv_zero'
#align polynomial.hasse_deriv_zero Polynomial.hasseDeriv_zero

theorem hasseDeriv_eq_zero_of_lt_natDegree (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    hasseDeriv n p = 0 := by
  rw [hasseDeriv_apply, sum_def]
  refine' Finset.sum_eq_zero fun x hx => _
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]
#align polynomial.hasse_deriv_eq_zero_of_lt_nat_degree Polynomial.hasseDeriv_eq_zero_of_lt_natDegree

theorem hasseDeriv_one' : hasseDeriv 1 f = derivative f := by
  simp only [hasseDeriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, Nat.choose_one_right,
    (Nat.cast_commute _ _).eq]
#align polynomial.hasse_deriv_one' Polynomial.hasseDeriv_one'

@[simp]
theorem hasseDeriv_one : @hasseDeriv R _ 1 = derivative :=
  LinearMap.ext <| hasseDeriv_one'
#align polynomial.hasse_deriv_one Polynomial.hasseDeriv_one

@[simp]
theorem hasseDeriv_monomial (n : ℕ) (r : R) :
    hasseDeriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) := by
  ext i
  simp only [hasseDeriv_coeff, coeff_monomial]
  by_cases hnik : n = i + k
  · rw [if_pos hnik, if_pos, ← hnik]
    apply tsub_eq_of_eq_add_rev
    rwa [add_comm]
  · rw [if_neg hnik, mul_zero]
    by_cases hkn : k ≤ n
    · rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik
      rw [if_neg hnik]
    · push_neg at hkn
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_mul, ite_self]
#align polynomial.hasse_deriv_monomial Polynomial.hasseDeriv_monomial

theorem hasseDeriv_C (r : R) (hk : 0 < k) : hasseDeriv k (C r) = 0 := by
  rw [← monomial_zero_left, hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, monomial_zero_right]
set_option linter.uppercaseLean3 false in
#align polynomial.hasse_deriv_C Polynomial.hasseDeriv_C

theorem hasseDeriv_apply_one (hk : 0 < k) : hasseDeriv k (1 : R[X]) = 0 := by
  rw [← C_1, hasseDeriv_C k _ hk]
#align polynomial.hasse_deriv_apply_one Polynomial.hasseDeriv_apply_one

theorem hasseDeriv_X (hk : 1 < k) : hasseDeriv k (X : R[X]) = 0 := by
  rw [← monomial_one_one_eq_X, hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero,
    zero_mul, monomial_zero_right]
set_option linter.uppercaseLean3 false in
#align polynomial.hasse_deriv_X Polynomial.hasseDeriv_X

theorem factorial_smul_hasseDeriv : ⇑(k ! • @hasseDeriv R _ k) = (@derivative R _)^[k] := by
  induction' k with k ih
  · rw [hasseDeriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
  ext f n : 2
  rw [iterate_succ_apply', ← ih]
  simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative,
    hasseDeriv_coeff, ← @choose_symm_add _ k]
  simp only [nsmul_eq_mul, factorial_succ, mul_assoc, succ_eq_add_one, ← add_assoc,
    add_right_comm n 1 k, ← cast_succ]
  rw [← (cast_commute (n + 1) (f.coeff (n + k + 1))).eq]
  simp only [← mul_assoc]
  norm_cast
  congr 2
  rw [mul_comm (k+1) _, mul_assoc, mul_assoc]
  congr 1
  have : n + k + 1 = n + (k + 1) := by apply add_assoc
  rw [← choose_symm_of_eq_add this, choose_succ_right_eq, mul_comm]
  congr
  rw [add_assoc, add_tsub_cancel_left]
#align polynomial.factorial_smul_hasse_deriv Polynomial.factorial_smul_hasseDeriv

theorem hasseDeriv_comp (k l : ℕ) :
    (@hasseDeriv R _ k).comp (hasseDeriv l) = (k + l).choose k • hasseDeriv (k + l) := by
  ext i : 2
  simp only [LinearMap.smul_apply, comp_apply, LinearMap.coe_comp, smul_monomial, hasseDeriv_apply,
    mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero, ←
    tsub_add_eq_tsub_tsub, add_comm l k]
  rw_mod_cast [nsmul_eq_mul]
  rw [← Nat.cast_mul]
  congr 2
  by_cases hikl : i < k + l
  · rw [choose_eq_zero_of_lt hikl, mul_zero]
    by_cases hil : i < l
    · rw [choose_eq_zero_of_lt hil, mul_zero]
    · push_neg at hil
      rw [← tsub_lt_iff_right hil] at hikl
      rw [choose_eq_zero_of_lt hikl, zero_mul]
  push_neg at hikl
  apply @cast_injective ℚ
  have h1 : l ≤ i := le_of_add_le_right hikl
  have h2 : k ≤ i - l := le_tsub_of_add_le_right hikl
  have h3 : k ≤ k + l := le_self_add
  push_cast
  rw [cast_choose ℚ h1, cast_choose ℚ h2, cast_choose ℚ h3, cast_choose ℚ hikl]
  rw [show i - (k + l) = i - l - k by rw [add_comm]; apply tsub_add_eq_tsub_tsub]
  simp only [add_tsub_cancel_left]
  field_simp; ring
#align polynomial.hasse_deriv_comp Polynomial.hasseDeriv_comp

theorem natDegree_hasseDeriv_le (p : R[X]) (n : ℕ) :
    natDegree (hasseDeriv n p) ≤ natDegree p - n := by
  classical
    rw [hasseDeriv_apply, sum_def]
    refine' (natDegree_sum_le _ _).trans _
    simp_rw [Function.comp, natDegree_monomial]
    rw [Finset.fold_ite, Finset.fold_const]
    · simp only [ite_self, max_eq_right, zero_le', Finset.fold_max_le, true_and_iff, and_imp,
        tsub_le_iff_right, mem_support_iff, Ne.def, Finset.mem_filter]
      intro x hx hx'
      have hxp : x ≤ p.natDegree := le_natDegree_of_ne_zero hx
      have hxn : n ≤ x := by
        contrapose! hx'
        simp [Nat.choose_eq_zero_of_lt hx']
      rwa [tsub_add_cancel_of_le (hxn.trans hxp)]
    · simp
#align polynomial.nat_degree_hasse_deriv_le Polynomial.natDegree_hasseDeriv_le

theorem natDegree_hasseDeriv [NoZeroSMulDivisors ℕ R] (p : R[X]) (n : ℕ) :
    natDegree (hasseDeriv n p) = natDegree p - n := by
  cases' lt_or_le p.natDegree n with hn hn
  · simpa [hasseDeriv_eq_zero_of_lt_natDegree, hn] using (tsub_eq_zero_of_le hn.le).symm
  · refine' map_natDegree_eq_sub _ _
    · exact fun h => hasseDeriv_eq_zero_of_lt_natDegree _ _
    · classical
        simp only [ite_eq_right_iff, Ne.def, natDegree_monomial, hasseDeriv_monomial]
        intro k c c0 hh
        -- this is where we use the `smul_eq_zero` from `NoZeroSMulDivisors`
        rw [← nsmul_eq_mul, smul_eq_zero, Nat.choose_eq_zero_iff] at hh
        exact (tsub_eq_zero_of_le (Or.resolve_right hh c0).le).symm
#align polynomial.nat_degree_hasse_deriv Polynomial.natDegree_hasseDeriv

section

open AddMonoidHom Finset.Nat

open Finset (antidiagonal mem_antidiagonal)

theorem hasseDeriv_mul (f g : R[X]) :
    hasseDeriv k (f * g) = ∑ ij in antidiagonal k, hasseDeriv ij.1 f * hasseDeriv ij.2 g := by
  let D k := (@hasseDeriv R _ k).toAddMonoidHom
  let Φ := @AddMonoidHom.mul R[X] _
  show
    (compHom (D k)).comp Φ f g =
      ∑ ij : ℕ × ℕ in antidiagonal k, ((compHom.comp ((compHom Φ) (D ij.1))).flip (D ij.2) f) g
  simp only [← finset_sum_apply]
  congr 2
  clear f g
  ext m r n s : 4
  simp only [finset_sum_apply, coe_mulLeft, coe_comp, flip_apply, Function.comp_apply,
             hasseDeriv_monomial, LinearMap.toAddMonoidHom_coe, compHom_apply_apply,
             coe_mul, monomial_mul_monomial]
  have aux :
    ∀ x : ℕ × ℕ,
      x ∈ antidiagonal k →
        monomial (m - x.1 + (n - x.2)) (↑(m.choose x.1) * r * (↑(n.choose x.2) * s)) =
          monomial (m + n - k) (↑(m.choose x.1) * ↑(n.choose x.2) * (r * s)) := by
    intro x hx
    rw [mem_antidiagonal] at hx
    subst hx
    by_cases hm : m < x.1
    · simp only [Nat.choose_eq_zero_of_lt hm, Nat.cast_zero, zero_mul,
                 monomial_zero_right]
    by_cases hn : n < x.2
    · simp only [Nat.choose_eq_zero_of_lt hn, Nat.cast_zero, zero_mul,
                 mul_zero, monomial_zero_right]
    push_neg at hm hn
    rw [tsub_add_eq_add_tsub hm, ← add_tsub_assoc_of_le hn, ← tsub_add_eq_tsub_tsub,
      add_comm x.2 x.1, mul_assoc, ← mul_assoc r, ← (Nat.cast_commute _ r).eq, mul_assoc, mul_assoc]
  rw [Finset.sum_congr rfl aux]
  rw [← map_sum, ← Finset.sum_mul]
  congr
  rw_mod_cast [← Nat.add_choose_eq]
#align polynomial.hasse_deriv_mul Polynomial.hasseDeriv_mul

end

end Polynomial

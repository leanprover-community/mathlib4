/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.Reduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Exact Wick-channel expansion for GMC(2)

This module connects the `MvPolynomial` expectation `GMC2.E` to the exact
finite-support multinomial channels used in the lowest-balanced-face theorem.  For a multiplicity
function `r` on `P.support`, its channel exponent is

`sum_s r(s) • s`.

The main theorem `E_pow_eq_channel_sum` says that `E (P^m)` is the sum over
`Finset.piAntidiag P.support m` of the multinomial coefficient, the exact
coefficient monomial, and the Wick weight of this accumulated exponent.
No support point is duplicated and no channel is separated after projection.
-/

open MvPolynomial Finset

namespace GMC2

/-- The accumulated bidegree of a multinomial channel. -/
noncomputable def channelExponent (S : Finset (Fin 2 →₀ ℕ))
    (r : (Fin 2 →₀ ℕ) → ℕ) : Fin 2 →₀ ℕ :=
  ∑ s ∈ S, r s • s

/-- The coefficient monomial attached to a multiplicity vector. -/
def channelCoefficient (P : MvPolynomial (Fin 2) ℂ)
    (r : (Fin 2 →₀ ℕ) → ℕ) : ℂ :=
  ∏ s ∈ P.support, P.coeff s ^ r s

/-- Rewrite the support-sum definition as the native `Finsupp.sum` over the coefficient
finitely-supported function. -/
theorem E_eq_finsupp_sum (P : MvPolynomial (Fin 2) ℂ) :
    E P = (AddMonoidAlgebra.coeff P).sum (fun s c => c * wt s) := by
  rw [MvPolynomial.sum_def]
  rfl

/-- `E P` may be summed over any finite superset of `P.support`; terms
outside the exact support have zero coefficient. -/
theorem E_eq_sum_of_subset {P : MvPolynomial (Fin 2) ℂ}
    {D : Finset (Fin 2 →₀ ℕ)} (h : P.support ⊆ D) :
    E P = ∑ s ∈ D, P.coeff s * wt s :=
  Finset.sum_subset h (fun s _ hs => by
    rw [MvPolynomial.notMem_support_iff.mp hs, zero_mul])

/-- `E` is additive.  This exposes the linearity hidden by its support-sum definition. -/
theorem E_add (P Q : MvPolynomial (Fin 2) ℂ) : E (P + Q) = E P + E Q := by
  classical
  have hPQ : (P + Q).support ⊆ (P + Q).support ∪ (P.support ∪ Q.support) :=
    fun s hs => Finset.mem_union_left _ hs
  have hP : P.support ⊆ (P + Q).support ∪ (P.support ∪ Q.support) :=
    fun s hs => Finset.mem_union_right _ (Finset.mem_union_left _ hs)
  have hQ : Q.support ⊆ (P + Q).support ∪ (P.support ∪ Q.support) :=
    fun s hs => Finset.mem_union_right _ (Finset.mem_union_right _ hs)
  rw [E_eq_sum_of_subset hPQ, E_eq_sum_of_subset hP, E_eq_sum_of_subset hQ,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [MvPolynomial.coeff_add]; ring

/-- `E` of a finite sum is the sum of the expectations. -/
theorem E_finset_sum {α : Type*} (S : Finset α)
    (f : α → MvPolynomial (Fin 2) ℂ) :
    E (∑ i ∈ S, f i) = ∑ i ∈ S, E (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [E]
  | @insert i S hi ih => simp [hi, E_add, ih]

/-- Wick evaluation of one exact monomial. -/
@[simp] theorem E_monomial (s : Fin 2 →₀ ℕ) (c : ℂ) :
    E (monomial s c) = c * wt s := by
  classical
  by_cases hc : c = 0
  · simp [hc, E]
  · simp [E, MvPolynomial.support_monomial, hc]

/-- A product of powered exact monomials remains one monomial; its exponent
and coefficient are the corresponding finite sums and products. -/
theorem prod_monomial_pow (S : Finset (Fin 2 →₀ ℕ))
    (c : (Fin 2 →₀ ℕ) → ℂ) (r : (Fin 2 →₀ ℕ) → ℕ) :
    (∏ s ∈ S, (monomial s (c s) : MvPolynomial (Fin 2) ℂ) ^ r s) =
      monomial (channelExponent S r) (∏ s ∈ S, c s ^ r s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [channelExponent]
  | @insert s S hs ih =>
      rw [Finset.prod_insert hs, ih]
      simp [hs, channelExponent, MvPolynomial.monomial_pow,
        MvPolynomial.monomial_mul]

/-- A product of exact monomials is a monomial, with exponent the sum and coefficient
the product.  This is the unpowered form of `prod_monomial_pow`. -/
theorem prod_monomial {α : Type*} (S : Finset α)
    (e : α → Fin 2 →₀ ℕ) (c : α → ℂ) :
    ∏ i ∈ S, (monomial (e i) (c i) : MvPolynomial (Fin 2) ℂ) =
      monomial (∑ i ∈ S, e i) (∏ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, ih, MvPolynomial.monomial_mul,
        Finset.sum_insert hi, Finset.prod_insert hi]

/-- Multiplying a monomial by a natural scalar inside `MvPolynomial` only
scales its coefficient. -/
theorem natCast_mul_monomial (n : ℕ) (s : Fin 2 →₀ ℕ) (c : ℂ) :
    (n : MvPolynomial (Fin 2) ℂ) * monomial s c =
      monomial s ((n : ℂ) * c) := by
  simp [MvPolynomial.monomial_eq, mul_assoc]

/-- **Exact Wick/multinomial bridge.**  The Gaussian moment of `P^m` is the
sum of all exact-support multiplicity channels.  Membership in `piAntidiag`
encodes both `sum_s r(s)=m` and `support(r) subset P.support`. -/
theorem E_pow_eq_channel_sum (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    E (P ^ m) =
      ∑ r ∈ Finset.piAntidiag P.support m,
        (Nat.multinomial P.support r : ℂ) * channelCoefficient P r *
          wt (channelExponent P.support r) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [E_finset_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [prod_monomial_pow]
  rw [natCast_mul_monomial]
  rw [E_monomial]
  simp only [channelCoefficient]

/-- The exact Wick expansion of `E (P ^ m)`, with `channelCoefficient` and
`channelExponent` unfolded.  This is the form the lowest-balanced-face argument consumes. -/
theorem wick_expansion (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    E (P ^ m) = ∑ r ∈ P.support.piAntidiag m,
      (Nat.multinomial P.support r : ℂ) *
        (∏ s ∈ P.support, P.coeff s ^ r s) *
          wt (∑ s ∈ P.support, r s • s) := by
  simpa only [channelCoefficient, channelExponent] using
    E_pow_eq_channel_sum P m

/-- Equation (1) of the lowest-balanced-face theorem in its explicit balanced-factorial form.
Unbalanced channels vanish; a balanced channel has Wick weight `A!`, where
`A` is either (equal) accumulated exponent. -/
theorem E_pow_eq_balanced_channel_sum (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    E (P ^ m) =
      ∑ r ∈ Finset.piAntidiag P.support m,
        if (channelExponent P.support r) 0 = (channelExponent P.support r) 1 then
          (Nat.multinomial P.support r : ℂ) * channelCoefficient P r *
            (Nat.factorial ((channelExponent P.support r) 0) : ℂ)
        else 0 := by
  rw [E_pow_eq_channel_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold wt
  split_ifs <;> simp

/-- A channel with nonzero accumulated charge contributes zero. -/
theorem wick_channel_zero_of_charge_ne
    (P : MvPolynomial (Fin 2) ℂ) (r : (Fin 2 →₀ ℕ) → ℕ)
    (hcharge : charge (channelExponent P.support r) ≠ 0) :
    (Nat.multinomial P.support r : ℂ) * channelCoefficient P r *
        wt (channelExponent P.support r) = 0 := by
    rw [wt_of_charge_ne hcharge, mul_zero]

/-- Charge is additive on the accumulated radial exponent of a channel. -/
theorem charge_radial {α : Type*} (S : Finset α) (r : α → ℕ)
    (exponent : α → Fin 2 →₀ ℕ) :
    charge (∑ i ∈ S, r i • exponent i) =
      ∑ i ∈ S, (r i : ℤ) * charge (exponent i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [charge]
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      simp only [charge, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      push_cast
      ring

/-- Exact Wick expansion restricted to the balanced-channel filter. -/
theorem wick_expansion_balanced (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    E (P ^ m) = ∑ r ∈ (P.support.piAntidiag m).filter
        (fun r => charge (∑ s ∈ P.support, r s • s) = 0),
      (Nat.multinomial P.support r : ℂ) *
        (∏ s ∈ P.support, P.coeff s ^ r s) *
          wt (∑ s ∈ P.support, r s • s) := by
  classical
  rw [wick_expansion]
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro r hr hnot
  rw [Finset.mem_filter, not_and] at hnot
  rw [wt_of_charge_ne (hnot hr), mul_zero]

end GMC2


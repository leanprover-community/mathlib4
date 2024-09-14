/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.LinearAlgebra.Finsupp

/-! # weights of Finsupp functions

The theory of multivariate polynomials and power series is built
on the type `σ →₀ ℕ` which gives the exponents of the monomials.
Many aspects of the theory (degree, order, graded ring structure)
require to classify these exponents according to their total sum
`∑  i, f i`, or variants, and this files provides some API for that.

## Weight

We fix a type `σ` and an `AddCommMonoid M`, as well as a function `w : σ → M`.

- `Finsupp.weight` of a finitely supported function `f : σ →₀ ℕ`
with respect to `w`: it is the sum `∑ (f i) • (w i)`.
It is an `AddMonoidHom` map defined using `Finsupp.linearCombination`.

- `Finsupp.le_weight`says that `f s ≤ f.weight w` when `M = ℕ``

- `Finsupp.le_weight_of_nonneg'` says that `w s ≤ f.weight w`
for `OrderedAddCommMonoid M`, when `f s ≠ 0` and all `w i` are nonnegative.

- `Finsupp.le_weight'` is the same statement for `CanonicallyOrderedAddCommMonoid M`.

- `NonTorsionWeight`: all values `w s` are non torsion in `M`.

- `Finsupp.weight_eq_zero_iff_eq_zero` says that `f.weight w = 0` iff
`f = 0` for `NonTorsion Weight w` and `CanonicallyOrderedAddCommMonoid M`.

## Degree

- `Finsupp.degree`:  the weight when all components of `w` are equal to `1 : ℕ`.
The present choice is to have it defined as a plain function.

- `Finsupp.degree_eq_zero_iff` says that `f.degree = 0` iff `f = 0`.

- `Finsupp.le_degree` says that `f s ≤ f.degree`.

- `Finsupp.degree_eq_weight_one` says `f.degree = f.weight 1`.
This is useful to access the additivity properties of `Finsupp.degree`


## TODO

* The relevant generality of these constructions is not clear.
It could probably be generalized to `w : σ → M` and `f : σ →₀ N`,
provided `N` is a commutative semiring and `M`is an `N`-module.

* Maybe `Finsupp.weight w` and `Finsupp.degree` should have similar types,
both `AddCommMonoidHom` or both functions.

-/

variable {σ M : Type*} (w : σ → M)

namespace Finsupp

section AddCommMonoid

variable [AddCommMonoid M]
/-- The `weight` of the finitely supported function `f : σ →₀ ℕ`
with respect to `w : σ → M` is the sum `∑(f i)•(w i)`. -/
noncomputable def weight : (σ →₀ ℕ) →+ M :=
  (Finsupp.linearCombination ℕ w).toAddMonoidHom

@[deprecated weight (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree := weight

theorem weight_apply (f : σ →₀ ℕ) :
    weight w f = Finsupp.sum f (fun i c => c • w i) := rfl

@[deprecated weight_apply (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree_apply := weight_apply

/-- A weight function is nontorsion if its values are not torsion. -/
class NonTorsionWeight (w : σ → M) : Prop where
  eq_zero_of_smul_eq_zero {n : ℕ} {s : σ} (h : n • w s = 0)  : n = 0

/-- Without zero divisors, nonzero weight is a `NonTorsionWeight` -/
theorem nonTorsionWeight_of [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight w where
  eq_zero_of_smul_eq_zero {n s} h := by
    rw [smul_eq_zero, or_iff_not_imp_right] at h
    exact h (hw s)

theorem NonTorsionWeight.ne_zero [NonTorsionWeight w] (s : σ) :
    w s ≠ 0 := fun h ↦ by
  rw [← one_smul ℕ (w s)] at h
  apply Nat.zero_ne_one.symm
  exact NonTorsionWeight.eq_zero_of_smul_eq_zero h

end AddCommMonoid

section OrderedAddCommMonoid

theorem le_weight (w : σ → ℕ) {s : σ} (hs : w s ≠ 0) (f : σ →₀ ℕ) :
    f s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases h : s ∈ f.support
  · rw [Finset.sum_eq_add_sum_diff_singleton h]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_mul_of_pos_right
    exact Nat.zero_lt_of_ne_zero hs
  · simp only [not_mem_support_iff] at h
    rw [h]
    apply zero_le

variable [OrderedAddCommMonoid M] (w : σ → M)

instance : SMulPosMono ℕ M :=
  ⟨fun b hb m m' h ↦ by
    rw [← Nat.add_sub_of_le h, add_smul]
    exact le_add_of_nonneg_right (nsmul_nonneg hb (m' - m))⟩

variable {w} in
theorem le_weight_of_ne_zero (hw : ∀ s, 0 ≤ w s) {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f := by
  classical
  simp only [weight_apply, Finsupp.sum]
  trans f s • w s
  · apply le_smul_of_one_le_left (hw s)
    exact Nat.one_le_iff_ne_zero.mpr hs
  · rw [← Finsupp.mem_support_iff] at hs
    rw [Finset.sum_eq_add_sum_diff_singleton hs]
    exact le_add_of_nonneg_right <| Finset.sum_nonneg <|
      fun i _ ↦ nsmul_nonneg (hw i) (f i)

end OrderedAddCommMonoid

section CanonicallyOrderedAddCommMonoid

variable {M : Type*} [CanonicallyOrderedAddCommMonoid M] (w : σ → M)

theorem le_weight_of_ne_zero' {s : σ} {f : σ →₀ ℕ} (hs : f s ≠ 0) :
    w s ≤ weight w f :=
  le_weight_of_ne_zero (fun _ ↦ zero_le _) hs

/-- If `M` is a `CanonicallyOrderedAddCommMonoid`, then `weight f` is zero iff `f=0. -/
theorem weight_eq_zero_iff_eq_zero
    (w : σ → M) [NonTorsionWeight w] {f : σ →₀ ℕ} :
    weight w f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    ext s
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hs
    apply NonTorsionWeight.ne_zero w _
    rw [← nonpos_iff_eq_zero, ← h]
    exact le_weight_of_ne_zero' w hs
  · intro h
    rw [h, map_zero]

end CanonicallyOrderedAddCommMonoid

/-- The degree of a finsupp function. -/
def degree (d : σ →₀ ℕ) := ∑ i ∈ d.support, d i

@[deprecated degree (since := "2024-07-20")]
alias _root_.MvPolynomial.degree := degree

lemma degree_eq_zero_iff (d : σ →₀ ℕ) : degree d = 0 ↔ d = 0 := by
  simp only [degree, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ne_eq, Decidable.not_imp_self,
    DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

@[deprecated degree_eq_zero_iff (since := "2024-07-20")]
alias _root_.MvPolynomial.degree_eq_zero_iff := degree_eq_zero_iff

@[simp]
theorem degree_zero : degree (0 : σ →₀ ℕ) = 0 := by rw [degree_eq_zero_iff]

theorem degree_eq_weight_one :
    degree (σ := σ) = weight 1 := by
  ext d
  simp only [degree, weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum]

@[deprecated degree_eq_weight_one (since := "2024-07-20")]
alias _root_.MvPolynomial.weightedDegree_one := degree_eq_weight_one

theorem le_degree (s : σ) (f : σ →₀ ℕ) : f s ≤ degree f  := by
  rw [degree_eq_weight_one]
  apply le_weight
  simp only [Pi.one_apply, ne_eq, one_ne_zero, not_false_eq_true]

end Finsupp

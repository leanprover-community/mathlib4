/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Monomial

/-!
# Summing over univariate polynomials

## Main definitions

* `Polynomial.sum p f`: sum `f` applied to the coefficients of `p`
-/

noncomputable section

open AddMonoidAlgebra Finset
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

section AddMonoidAlgebra

variable (R)

end AddMonoidAlgebra

open Finset

/-- Summing the values of a function applied to the coefficients of a polynomial -/
def sum {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) : S :=
  ∑ n ∈ p.support, f n (p.coeff n)

theorem sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) :=
  rfl

theorem sum_eq_of_subset {S : Type*} [AddCommMonoid S] {p : R[X]} (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) {s : Finset ℕ} (hs : p.support ⊆ s) :
    p.sum f = ∑ n ∈ s, f n (p.coeff n) :=
  Finsupp.sum_of_support_subset _ hs f (fun i _ ↦ hf i)

/-- Expressing the product of two polynomials as a double sum. -/
theorem mul_eq_sum_sum :
    p * q = ∑ i ∈ p.support, q.sum fun j a => (monomial (i + j)) (p.coeff i * a) := by
  apply toFinsupp_injective
  rcases p with ⟨⟩; rcases q with ⟨⟩
  simp_rw [sum, coeff, toFinsupp_sum, support, toFinsupp_mul, toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

@[simp]
theorem sum_zero_index {S : Type*} [AddCommMonoid S] (f : ℕ → R → S) : (0 : R[X]).sum f = 0 := by
  simp [sum]

@[simp]
theorem sum_monomial_index {S : Type*} [AddCommMonoid S] {n : ℕ} (a : R) (f : ℕ → R → S)
    (hf : f n 0 = 0) : (monomial n a : R[X]).sum f = f n a :=
  Finsupp.sum_single_index hf

@[simp]
theorem sum_C_index {a} {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
    (C a).sum f = f 0 a :=
  sum_monomial_index a f h

-- the assumption `hf` is only necessary when the ring is trivial
@[simp]
theorem sum_X_index {S : Type*} [AddCommMonoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
    (X : R[X]).sum f = f 1 1 :=
  sum_monomial_index 1 f hf

theorem sum_add_index {S : Type*} [AddCommMonoid S] (p q : R[X]) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) (h_add : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (p + q).sum f = p.sum f + q.sum f := by
  rw [show p + q = ⟨p.toFinsupp + q.toFinsupp⟩ by ext; simp]
  exact Finsupp.sum_add_index (fun i _ ↦ hf i) (fun a _ b₁ b₂ ↦ h_add a b₁ b₂)

theorem sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    p.sum (f + g) = p.sum f + p.sum g := by simp [sum_def, Finset.sum_add_distrib]

theorem sum_add {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g :=
  sum_add' _ _ _

theorem sum_smul_index {S : Type*} [AddCommMonoid S] (p : R[X]) (b : R) (f : ℕ → R → S)
    (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b * a) :=
  Finsupp.sum_smul_index hf

theorem sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X]) (b : T)
    (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b • a) :=
  Finsupp.sum_smul_index' hf

protected theorem smul_sum {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : R[X]) (b : T)
    (f : ℕ → R → S) : b • p.sum f = p.sum fun n a => b • f n a :=
  Finsupp.smul_sum

@[simp]
theorem sum_monomial_eq : ∀ p : R[X], (p.sum fun n a => monomial n a) = p
  | ⟨_p⟩ => (ofFinsupp_sum _ _).symm.trans (congr_arg _ <| Finsupp.sum_single _)

theorem sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fun n a => C a * X ^ n) = p := by
  simp_rw [C_mul_X_pow_eq_monomial, sum_monomial_eq]

@[elab_as_elim]
protected theorem induction_on {M : R[X] → Prop} (p : R[X]) (h_C : ∀ a, M (C a))
    (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (C a * X ^ n) → M (C a * X ^ (n + 1))) : M p := by
  have A : ∀ {n : ℕ} {a}, M (C a * X ^ n) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, mul_one]; exact h_C a
    | succ n ih => exact h_monomial _ _ ih
  have B : ∀ s : Finset ℕ, M (s.sum fun n : ℕ => C (p.coeff n) * X ^ n) := by
    apply Finset.induction
    · convert h_C 0
      exact C_0.symm
    · intro n s ns ih
      rw [sum_insert ns]
      exact h_add _ _ A ih
  rw [← sum_C_mul_X_pow_eq p, Polynomial.sum]
  exact B (support p)

/-- To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_elim]
protected theorem induction_on' {M : R[X] → Prop} (p : R[X]) (h_add : ∀ p q, M p → M q → M (p + q))
    (h_monomial : ∀ (n : ℕ) (a : R), M (monomial n a)) : M p :=
  Polynomial.induction_on p (h_monomial 0) h_add fun n a _h =>
    by rw [C_mul_X_pow_eq_monomial]; exact h_monomial _ _

end Semiring

end Polynomial

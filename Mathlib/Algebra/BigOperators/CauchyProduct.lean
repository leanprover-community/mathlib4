/-
Copyright (c) 2025 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.Ring

/-!
# Cauchy Product (Finite Antidiagonal Convolution)

For types with `Finset.HasAntidiagonal` (e.g., ℕ, ℕ × ℕ), convolution is a finite sum
over the antidiagonal. This gives a purely algebraic ring structure without requiring
topology or `tsum` convergence.

## Main Definitions

* `CauchyProduct.apply`: `(a ⋆ b) n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2`
* `CauchyProduct.one`: The multiplicative identity `δ₀`, where `δ₀(0) = 1` and `δ₀(g) = 0`
  for `g ≠ 0`

## Main Results

* `CauchyProduct.assoc`: Associativity via `Finset.sum_nbij'`
* `CauchyProduct.one_mul`, `CauchyProduct.mul_one`: Identity laws
* `CauchyProduct.comm`: Commutativity for `[CommSemiring R]`
* `CauchyProduct.left_distrib`, `CauchyProduct.right_distrib`: Distributivity

## Notation

* `a ⋆ b` : Cauchy product convolution

## Connection to DiscreteConvolution

For types with `HasAntidiagonal`, the `tsum`-based `DiscreteConvolution.addRingConvolution`
equals `CauchyProduct.apply`. See `DiscreteConvolution.addRingConvolution_eq_cauchyProduct`
in `Mathlib.Topology.Algebra.InfiniteSum.Convolution.Basic`.

-/

@[expose] public section

open scoped BigOperators

namespace CauchyProduct

variable {G : Type*} {R : Type*}

/-! ### Product Definition -/

section Product

variable [AddMonoid G] [Finset.HasAntidiagonal G] [Semiring R]

/-- Cauchy product (convolution) via finite antidiagonal sum. -/
def apply (a b : G → R) : G → R :=
  fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

/-- Notation for Cauchy product convolution. -/
scoped notation:70 a:70 " ⋆ " b:71 => apply a b

theorem apply_eq (a b : G → R) (n : G) :
    (a ⋆ b) n = ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2 := rfl

/-! ### Ring Axioms -/

theorem left_distrib (a b c : G → R) : a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  ext n; simp only [Pi.add_apply, apply_eq, mul_add, Finset.sum_add_distrib]

theorem right_distrib (a b c : G → R) : (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  ext n; simp only [apply_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp]
theorem zero_mul (a : G → R) : (0 : G → R) ⋆ a = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]

@[simp]
theorem mul_zero (a : G → R) : a ⋆ (0 : G → R) = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-! ### Associativity via bijection on triple sums -/

/-- Associativity of Cauchy product, proved via bijection on sigma types. -/
theorem assoc (a b c : G → R) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  ext n
  simp only [apply_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals intro x hx
  all_goals simp_all only [Finset.mem_sigma, Finset.mem_antidiagonal, Prod.mk.eta, Sigma.eta]
  · exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  · exact ⟨by rw [← hx.1, ← hx.2, add_assoc], trivial⟩
  · exact mul_assoc _ _ _

theorem smul_mul (c : R) (a b : G → R) : (c • a) ⋆ b = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Product

/-! ### Identity Element -/

section Identity

variable [AddMonoid G] [DecidableEq G] [Semiring R]

/-- The multiplicative identity: `δ₀(0) = 1`, `δ₀(g) = 0` for `g ≠ 0`. -/
def one : G → R := Pi.single 0 1

@[simp]
theorem one_apply_zero : (one : G → R) 0 = 1 := Pi.single_eq_same 0 1

theorem one_apply_ne {g : G} (hg : g ≠ 0) : (one : G → R) g = 0 := Pi.single_eq_of_ne hg 1

end Identity

/-! ### Identity Laws -/

section IdentityAntidiagonal

variable [AddMonoid G] [DecidableEq G] [Finset.HasAntidiagonal G] [Semiring R]

theorem one_mul (a : G → R) : one ⋆ a = a := by
  ext n; simp only [apply_eq, one]
  rw [Finset.sum_eq_single (0, n), Pi.single_eq_same, _root_.one_mul]
  · intro ⟨x, y⟩ hxy hne
    simp only [Finset.mem_antidiagonal] at hxy; subst hxy
    simp [show x ≠ 0 from fun h => hne (by simp [h])]
  · simp [Finset.mem_antidiagonal]

theorem mul_one (a : G → R) : a ⋆ one = a := by
  ext n; simp only [apply_eq, one]
  rw [Finset.sum_eq_single (n, 0), Pi.single_eq_same, _root_.mul_one]
  · intro ⟨x, y⟩ hxy hne
    simp only [Finset.mem_antidiagonal] at hxy; subst hxy
    simp [show y ≠ 0 from fun h => hne (by simp only [h, add_zero])]
  · simp [Finset.mem_antidiagonal]

end IdentityAntidiagonal

/-! ### Commutativity -/

section Comm

variable [AddCommMonoid G] [Finset.HasAntidiagonal G] [CommSemiring R]

theorem comm (a b : G → R) : a ⋆ b = b ⋆ a := by
  ext n; simp only [apply_eq]
  rw [← Finset.map_swap_antidiagonal (n := n), Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.fst_swap,
    Prod.snd_swap, Finset.map_swap_antidiagonal, mul_comm]

theorem mul_smul (c : R) (a b : G → R) : a ⋆ (c • b) = c • (a ⋆ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro kl _; ring

end Comm

end CauchyProduct

end

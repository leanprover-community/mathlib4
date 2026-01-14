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

For types with `Finset.HasMulAntidiagonal` or `Finset.HasAntidiagonal`, convolution is a finite sum
over the antidiagonal. This gives a purely algebraic ring structure without requiring
topology or `tsum` convergence.

The multiplicative version `MulCauchyProduct` uses `Finset.mulAntidiagonal`, and the additive
version `CauchyProduct` uses `Finset.antidiagonal`. The additive versions are generated via
`@[to_additive]`.

## Main Results

* `MulCauchyProduct.assoc` / `CauchyProduct.assoc`: Associativity via `Finset.sum_nbij'`
* `MulCauchyProduct.one_mul`, `MulCauchyProduct.mul_one`: Identity laws
* `MulCauchyProduct.comm` / `CauchyProduct.comm`: Commutativity for `[CommSemiring R]`
* `MulCauchyProduct.left_distrib`, `MulCauchyProduct.right_distrib`: Distributivity

## Notation

* `a ⋆ₘ b` : Multiplicative Cauchy product convolution (over `mulAntidiagonal`)
* `a ⋆ b` : Additive Cauchy product convolution (over `antidiagonal`)

## Connection to DiscreteConvolution

For types with `HasAntidiagonal`, the `tsum`-based `DiscreteConvolution.addRingConvolution`
equals `CauchyProduct.apply`. See `DiscreteConvolution.addRingConvolution_eq_cauchyProduct`
in `Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution`.

-/

@[expose] public section

open scoped BigOperators

namespace MulCauchyProduct

variable {M : Type*} {R : Type*}

/-! ### Product Definition -/

section Product

variable [Monoid M] [Finset.HasMulAntidiagonal M] [Semiring R]

/-- Multiplicative Cauchy product (convolution) via finite multiplicative antidiagonal sum. -/
@[to_additive (dont_translate := R) CauchyProduct.apply
  /-- Cauchy product (convolution) via finite antidiagonal sum. -/]
def apply (a b : M → R) : M → R :=
  fun n => ∑ kl ∈ Finset.mulAntidiagonal n, a kl.1 * b kl.2

/-- Notation for multiplicative Cauchy product convolution. -/
scoped notation:70 a:70 " ⋆ₘ " b:71 => apply a b

@[to_additive (dont_translate := R) CauchyProduct.apply_eq]
theorem apply_eq (a b : M → R) (n : M) :
    (a ⋆ₘ b) n = ∑ kl ∈ Finset.mulAntidiagonal n, a kl.1 * b kl.2 := rfl

/-! ### Ring Axioms -/

@[to_additive (dont_translate := R) CauchyProduct.left_distrib]
theorem left_distrib (a b c : M → R) : a ⋆ₘ (b + c) = a ⋆ₘ b + a ⋆ₘ c := by
  ext n; simp only [Pi.add_apply, apply_eq, mul_add, Finset.sum_add_distrib]

@[to_additive (dont_translate := R) CauchyProduct.right_distrib]
theorem right_distrib (a b c : M → R) : (a + b) ⋆ₘ c = a ⋆ₘ c + b ⋆ₘ c := by
  ext n; simp only [apply_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[to_additive (dont_translate := R) (attr := simp) CauchyProduct.zero_mul]
theorem zero_mul (a : M → R) : (0 : M → R) ⋆ₘ a = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]

@[to_additive (dont_translate := R) (attr := simp) CauchyProduct.mul_zero]
theorem mul_zero (a : M → R) : a ⋆ₘ (0 : M → R) = 0 := by
  ext n; simp only [apply_eq, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]

/-! ### Associativity via bijection on triple sums -/

/-- Associativity of multiplicative Cauchy product, proved via bijection on sigma types. -/
@[to_additive (dont_translate := R) CauchyProduct.assoc
  /-- Associativity of Cauchy product, proved via bijection on sigma types. -/]
theorem assoc (a b c : M → R) : (a ⋆ₘ b) ⋆ₘ c = a ⋆ₘ (b ⋆ₘ c) := by
  ext n
  simp only [apply_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun x => ⟨(x.2.1, x.2.2 * x.1.2), (x.2.2, x.1.2)⟩)
    (fun x => ⟨(x.1.1 * x.2.1, x.2.2), (x.1.1, x.2.1)⟩)
    ?_ ?_ ?_ ?_ ?_
  all_goals intro x hx
  all_goals simp_all only [Finset.mem_sigma, Finset.mem_mulAntidiagonal, Prod.mk.eta, Sigma.eta]
  · exact ⟨by rw [← hx.1, ← hx.2, mul_assoc], trivial⟩
  · exact ⟨by rw [← hx.1, ← hx.2, mul_assoc], trivial⟩
  · exact mul_assoc (a x.2.1) (b x.2.2) (c x.1.2)

@[to_additive (dont_translate := R) CauchyProduct.smul_mul]
theorem smul_mul (c : R) (a b : M → R) : (c • a) ⋆ₘ b = c • (a ⋆ₘ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Product

/-! ### Identity Element -/

section Identity

variable [Monoid M] [DecidableEq M] [Semiring R]

/-- The multiplicative identity for mul Cauchy product: `δ₁(1) = 1`, `δ₁(g) = 0` for `g ≠ 1`. -/
@[to_additive (dont_translate := R) CauchyProduct.one
  /-- The multiplicative identity for Cauchy product: `δ₀(0) = 1`, `δ₀(g) = 0` for `g ≠ 0`. -/]
def one : M → R := Pi.single 1 1

@[to_additive (dont_translate := R) (attr := simp) CauchyProduct.one_apply_zero]
theorem one_apply_one : (one : M → R) 1 = 1 := Pi.single_eq_same 1 1

@[to_additive (dont_translate := R) CauchyProduct.one_apply_ne]
theorem one_apply_ne {g : M} (hg : g ≠ 1) : (one : M → R) g = 0 := Pi.single_eq_of_ne hg 1

end Identity

/-! ### Identity Laws -/

section IdentityMulAntidiagonal

variable [Monoid M] [DecidableEq M] [Finset.HasMulAntidiagonal M] [Semiring R]

@[to_additive (dont_translate := R) CauchyProduct.one_mul]
theorem one_mul (a : M → R) : one ⋆ₘ a = a := by
  ext n; simp only [apply_eq, one]
  rw [Finset.sum_eq_single (1, n), Pi.single_eq_same, _root_.one_mul]
  · intro ⟨x, y⟩ hxy hne
    simp only [Finset.mem_mulAntidiagonal] at hxy; subst hxy
    simp [show x ≠ 1 from fun h => hne (by simp [h])]
  · simp [Finset.mem_mulAntidiagonal]

@[to_additive (dont_translate := R) CauchyProduct.mul_one]
theorem mul_one (a : M → R) : a ⋆ₘ one = a := by
  ext n; simp only [apply_eq, one]
  rw [Finset.sum_eq_single (n, 1), Pi.single_eq_same, _root_.mul_one]
  · intro ⟨x, y⟩ hxy hne
    simp only [Finset.mem_mulAntidiagonal] at hxy
    have hy : y ≠ 1 := fun h => hne (by simp only [← hxy, h, _root_.mul_one])
    simp [Pi.single_eq_of_ne hy]
  · simp [Finset.mem_mulAntidiagonal]

end IdentityMulAntidiagonal

/-! ### Commutativity -/

section Comm

variable [CommMonoid M] [Finset.HasMulAntidiagonal M] [CommSemiring R]

@[to_additive (dont_translate := R) CauchyProduct.comm]
theorem comm (a b : M → R) : a ⋆ₘ b = b ⋆ₘ a := by
  ext n; simp only [apply_eq]
  rw [← Finset.map_swap_mulAntidiagonal (n := n), Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.fst_swap,
    Prod.snd_swap, Finset.map_swap_mulAntidiagonal, mul_comm]

@[to_additive (dont_translate := R) CauchyProduct.mul_smul]
theorem mul_smul (c : R) (a b : M → R) : a ⋆ₘ (c • b) = c • (a ⋆ₘ b) := by
  ext n; simp only [apply_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro kl _; ring

end Comm

end MulCauchyProduct

/-! ### Additive notation -/

namespace CauchyProduct

/-- Notation for additive Cauchy product convolution. -/
scoped notation:70 a:70 " ⋆ " b:71 => apply a b

end CauchyProduct

end

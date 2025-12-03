/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions

* `ArithmeticFunction R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
* An arithmetic function `f` `IsMultiplicative` when `x.Coprime y → f (x * y) = f x * f y`.
* The pointwise operations `pmul` and `ppow` differ from the multiplication
  and power instances on `ArithmeticFunction R`, which use Dirichlet multiplication.
* `ζ` is the arithmetic function such that `ζ x = 1` for `0 < x`.
* `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
* `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
* `id` is the identity arithmetic function on `ℕ`.
* `ω n` is the number of distinct prime factors of `n`.
* `Ω n` is the number of prime factors of `n` counted with multiplicity.
* `μ` is the Möbius function (spelled `moebius` in code).

## Main Results

* Several forms of Möbius inversion:
* `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
* And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
* `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Notation

The arithmetic functions `ζ`, `σ`, `ω`, `Ω` and `μ` have Greek letter names.
This notation is scpoed to the separate locales `ArithmeticFunction.zeta` for `ζ`,
`ArithmeticFunction.sigma` for `σ`, `ArithmeticFunction.omega` for `ω`,
`ArithmeticFunction.Omega` for `Ω`, and `ArithmeticFunction.Moebius` for `μ`,
to allow for selective access.

The arithmetic function $n \mapsto \prod_{p \mid n} f(p)$ is given custom notation
`∏ᵖ p ∣ n, f p` when applied to `n`.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

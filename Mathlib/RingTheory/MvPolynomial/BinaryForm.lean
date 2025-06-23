/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Binary forms

A binary form of degree `d` is a homogeneous polynomial in two variables of degree `d`.

## Main definitions

- `BinaryForm R d` is the type of binary forms over a commutative ring `R` of degree `d`.
- `BinaryForm.basis R d` is the basis of `BinaryForm R d` consisting of the monomials
  `X ^ i * Y ^ (d - i)` for `i : Fin (d + 1)`.

-/


universe u

theorem Finsupp.degree_eq_sum {ι : Type*} [DecidableEq ι] [Fintype ι]
    {R : Type u} [AddCommMonoid R] (f : ι →₀ R) :
    f.degree = ∑ i, f i := by
  rw [degree, Finset.sum_congr_of_eq_on_inter] <;> simp

@[simp] theorem Finsupp.mapDomain.linearEquiv_symm {α α' M R : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (f : α ≃ α') :
    (mapDomain.linearEquiv M R f).symm = mapDomain.linearEquiv M R f.symm := rfl

@[simp] theorem Finsupp.mapDomain.linearEquiv_single
    {α α' M R : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (f : α ≃ α') (i : α) (a : M) :
    mapDomain.linearEquiv M R f (single i a) = single (f i) a := by
  simp [mapDomain.linearEquiv]

@[simp] theorem Finsupp.supportedEquivFinsupp_symm_single
    {α M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (s : Set α) (i : s) (a : M) :
    ((supportedEquivFinsupp (R := R) s).symm (single i a) : α →₀ M) = single ↑i a := by
  classical rw [supportedEquivFinsupp_symm_apply_coe, extendDomain_single]


open MvPolynomial Finsupp

/-- A binary form of degree `d` is a homogeneous polynomial in two variables of degree `d`. -/
abbrev BinaryForm (R : Type u) [CommSemiring R] (d : ℕ) : Type u :=
  homogeneousSubmodule (Fin 2) R d

namespace BinaryForm

variable (R : Type u) [CommSemiring R] (d : ℕ)

/-- The bijection from `Fin (d + 1)` to degrees of bivariate monomials with degree `d`.
`i : Fin (d + 1)` is sent to the degree of `X ^ i * Y ^ (d - i)`. -/
@[simps!] noncomputable def degreeEquiv : Fin (d + 1) ≃ { c : Fin 2 →₀ ℕ // c.degree = d } where
  toFun i := ⟨single 0 (i : ℕ) + single 1 (d - i),
    by simpa [-single_tsub] using Nat.add_sub_cancel' i.is_le⟩
  invFun c := ⟨c.val 0, Nat.lt_succ_of_le <| by convert le_degree 0 c.val; exact c.2.symm⟩
  left_inv i := by simp
  right_inv c := by
    ext i; fin_cases i
    · simp
    · simp [← c.2, degree_eq_sum]

/-- A function `Fin (d + 1) → R` specifying the coefficients gives a binary form of degree `d`.
The `i`ᵗʰ coefficient is the coefficient of `X ^ i * Y ^ (d - i)`. -/
noncomputable def of : (Fin (d + 1) → R) ≃ₗ[R] BinaryForm R d :=
  (linearEquivFunOnFinite _ _ _).symm ≪≫ₗ
    mapDomain.linearEquiv _ _ (degreeEquiv d) ≪≫ₗ
    (supportedEquivFinsupp _).symm ≪≫ₗ
    LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported _ _ _).symm

@[simp] lemma of_single (i : Fin (d + 1)) :
    (of R d (Pi.single i 1) : MvPolynomial (Fin 2) R) = X 0 ^ (i : ℕ) * X 1 ^ (d - i) := by
  simp only [of, LinearEquiv.trans_apply, linearEquivFunOnFinite_symm_single,
    mapDomain.linearEquiv_single, Fin.isValue, X_pow_eq_monomial, monomial_mul, mul_one]
  convert LinearEquiv.coe_ofEq_apply ..
  convert (supportedEquivFinsupp_symm_single ..).symm
  rfl

/-- `BinaryForm R d` has a basis indexed by `Fin (d + 1)` where `i` maps to `X ^ i * Y ^ (d - i)`.
-/
noncomputable def basis : Basis (Fin (d + 1)) R (BinaryForm R d) :=
  .ofEquivFun (of R d).symm

@[simp] lemma basis_apply (i : Fin (d + 1)) :
    (basis R d i : MvPolynomial (Fin 2) R) = X 0 ^ (i : ℕ) * X 1 ^ (d - i) := by
  simp [basis]

end BinaryForm

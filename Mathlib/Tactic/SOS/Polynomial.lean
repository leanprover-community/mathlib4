/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import SOS.Core
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Real.Basic

/-!
# Interpreting Hex polynomials in Mathlib

This file gives the narrow real interpretation of `Hex.MvPoly` operations needed by the
certificate verifier.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

open scoped BigOperators

open Hex
open Hex.MvPoly

noncomputable section

variable {n : Nat}

/-!
This is deliberately narrower than `hex-mv-poly-mathlib`: SOS needs only an
interpretation of its `Rat` polynomials in `ℝ` and the operation laws consumed
by the certificate verifier.  It does not need a general ring equivalence or
the wider `MvPolynomial` correspondence API.
-/

/-- A fixed-arity exponent vector as Mathlib's finitely supported exponent
function. -/
def monoEquiv : Mono n ≃ (Fin n →₀ Nat) where
  toFun m := Finsupp.equivFunOnFinite.symm fun i => m[i]
  invFun d := Hex.Vector.ofFn' fun i => d i
  left_inv m := by
    apply Vector.ext
    intro i
    simp
  right_inv d := by
    apply Finsupp.ext
    intro i
    simp

private theorem monoEquiv_apply (m : Mono n) (i : Fin n) :
    monoEquiv m i = m[i] := by
  rfl

private theorem monoEquiv_zero :
    monoEquiv (Mono.zero : Mono n) = 0 := by
  apply Finsupp.ext
  intro i
  simp [Mono.zero, monoEquiv_apply]

private theorem monoEquiv_mul (a b : Mono n) :
    monoEquiv (Mono.mul a b) = monoEquiv a + monoEquiv b := by
  apply Finsupp.ext
  intro i
  simp [Mono.mul, monoEquiv_apply]

private theorem monoEquiv_unit (i : Fin n) :
    monoEquiv (Mono.unit i) = Finsupp.single i 1 := by
  apply Finsupp.ext
  intro j
  by_cases h : j = i <;> simp [Mono.unit, monoEquiv_apply, h]

private def monoPairEquiv :
    (Mono n × Mono n) ≃ ((Fin n →₀ Nat) × (Fin n →₀ Nat)) :=
  Equiv.prodCongr monoEquiv monoEquiv

private theorem monoPairEmbedding_apply (ab : Mono n × Mono n) :
    monoPairEquiv.toEmbedding ab =
      (monoEquiv ab.1, monoEquiv ab.2) := by
  rfl

attribute [local simp] monoEquiv_apply monoEquiv_zero monoEquiv_mul
  monoEquiv_unit monoPairEmbedding_apply

/-- Interpret an SOS engine polynomial as a Mathlib multivariate polynomial.
Only this one-way map is needed for soundness. -/
def toMvPolynomial (p : CMvPolynomial n Rat) : MvPolynomial (Fin n) Rat :=
  p.monomials.toFinset.sum fun m =>
    MvPolynomial.monomial (monoEquiv m) (Hex.MvPoly.coeff m p)

private theorem coeff_toMvPolynomial (m : Mono n)
    (p : CMvPolynomial n Rat) :
    MvPolynomial.coeff (monoEquiv m) (toMvPolynomial p) =
      Hex.MvPoly.coeff m p := by
  rw [toMvPolynomial, MvPolynomial.coeff_sum]
  by_cases hm : m ∈ p.monomials
  · simp [MvPolynomial.coeff_monomial, monoEquiv.injective.eq_iff,
      hm]
  · have hc : Hex.MvPoly.coeff m p = 0 := by
      exact Classical.not_not.mp
        ((Hex.MvPoly.mem_monomials_iff m p).not.mp hm)
    simp [MvPolynomial.coeff_monomial, monoEquiv.injective.eq_iff,
      hm, hc]

attribute [local simp] coeff_toMvPolynomial

@[simp] theorem toMvPolynomial_zero :
    toMvPolynomial (0 : CMvPolynomial n Rat) = 0 := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp

@[simp] theorem toMvPolynomial_add (p q : CMvPolynomial n Rat) :
    toMvPolynomial (p + q) = toMvPolynomial p + toMvPolynomial q := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [Hex.MvPoly.coeff_add]

@[simp] theorem toMvPolynomial_C (c : Rat) :
    toMvPolynomial (C c : CMvPolynomial n Rat) = MvPolynomial.C c := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, Hex.MvPoly.coeff_C,
    MvPolynomial.coeff_C]
  by_cases h : m = Mono.zero
  · subst m
    simp
  · have hz : (0 : Fin n →₀ Nat) ≠ monoEquiv m := by
      intro heq
      apply h
      apply monoEquiv.injective
      simpa using heq.symm
    simp [h, hz]

@[simp] theorem toMvPolynomial_X (i : Fin n) :
    toMvPolynomial (X i : CMvPolynomial n Rat) = MvPolynomial.X i := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, Hex.MvPoly.coeff_X, MvPolynomial.coeff_X,
    ← monoEquiv_unit]
  by_cases h : m = Mono.unit i
  · subst m
    simp
  · have h' : monoEquiv (Mono.unit i) ≠ monoEquiv m := by
      intro heq
      exact h (monoEquiv.injective heq).symm
    rw [_root_.ite_eq_right h, _root_.ite_eq_right h']

@[simp] theorem toMvPolynomial_one :
    toMvPolynomial (1 : CMvPolynomial n Rat) = 1 := by
  rw [show (1 : CMvPolynomial n Rat) = C 1 from rfl,
    toMvPolynomial_C, MvPolynomial.C_1]

@[simp] theorem toMvPolynomial_mul (p q : CMvPolynomial n Rat) :
    toMvPolynomial (p * q) = toMvPolynomial p * toMvPolynomial q := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  rw [coeff_toMvPolynomial, Hex.MvPoly.coeff_mul,
    MvPolynomial.coeff_mul]
  have hanti :
      (Mono.splits m).toFinset.map monoPairEquiv.toEmbedding =
        Finset.antidiagonal (monoEquiv m) := by
    ext ab
    constructor
    · intro hab
      rcases Finset.mem_map.mp hab with ⟨xy, hxy, rfl⟩
      rw [Finset.mem_antidiagonal, monoPairEmbedding_apply,
        ← monoEquiv_mul]
      exact congrArg monoEquiv ((Mono.splits_mem_iff ..).mp
        (List.mem_toFinset.mp hxy))
    · intro hab
      rw [Finset.mem_antidiagonal] at hab
      let xy : Mono n × Mono n :=
        (monoEquiv.symm ab.1, monoEquiv.symm ab.2)
      apply Finset.mem_map.mpr
      refine ⟨xy, ?_, ?_⟩
      · apply List.mem_toFinset.mpr
        apply (Mono.splits_mem_iff ..).mpr
        apply monoEquiv.injective
        simpa [xy] using hab
      · apply Prod.ext <;> simp [xy]
  rw [← hanti, Finset.sum_map]
  simp_rw [monoPairEmbedding_apply, coeff_toMvPolynomial]
  change
    (Mono.splits m).foldl
        (fun acc ab => acc + Hex.MvPoly.coeff ab.1 p *
          Hex.MvPoly.coeff ab.2 q) 0 =
      ∑ ab ∈ (Mono.splits m).toFinset,
        Hex.MvPoly.coeff ab.1 p * Hex.MvPoly.coeff ab.2 q
  rw [List.sum_toFinset _ (Mono.splits_nodup m),
    List.sum_eq_foldl, List.foldl_map]

@[simp] theorem toMvPolynomial_neg (p : CMvPolynomial n Rat) :
    toMvPolynomial (-p) = -toMvPolynomial p := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [Hex.MvPoly.coeff_neg]

@[simp] theorem toMvPolynomial_sub (p q : CMvPolynomial n Rat) :
    toMvPolynomial (p - q) = toMvPolynomial p - toMvPolynomial q := by
  apply MvPolynomial.ext
  intro d
  rcases monoEquiv.surjective d with ⟨m, rfl⟩
  simp [Hex.MvPoly.coeff_sub]

@[simp] theorem toMvPolynomial_pow (p : CMvPolynomial n Rat) (k : Nat) :
    toMvPolynomial (p ^ k) = toMvPolynomial p ^ k := by
  induction k with
  | zero =>
      rw [_root_.pow_zero (toMvPolynomial p)]
      have hp : p ^ 0 = (1 : CMvPolynomial n Rat) := by
        change Hex.MvPoly.npowBySq p 0 = 1
        rw [Hex.MvPoly.npowBySq]
      rw [hp, toMvPolynomial_one]
  | succ k ih =>
      rw [Hex.MvPoly.pow_succ p k, toMvPolynomial_mul, ih,
        _root_.pow_succ]

/-- Real evaluation used by the SOS soundness layer. -/
def aeval (x : Fin n → ℝ) (p : CMvPolynomial n Rat) : ℝ :=
  MvPolynomial.aeval x (toMvPolynomial p)

@[simp] theorem aeval_zero (x : Fin n → ℝ) :
    aeval x (0 : CMvPolynomial n Rat) = 0 := by
  simp [aeval]

@[simp] theorem aeval_one (x : Fin n → ℝ) :
    aeval x (1 : CMvPolynomial n Rat) = 1 := by
  simp [aeval]

@[simp] theorem aeval_add (x : Fin n → ℝ)
    (p q : CMvPolynomial n Rat) :
    aeval x (p + q) = aeval x p + aeval x q := by
  simp [aeval]

@[simp] theorem aeval_mul (x : Fin n → ℝ)
    (p q : CMvPolynomial n Rat) :
    aeval x (p * q) = aeval x p * aeval x q := by
  simp [aeval]

@[simp] theorem aeval_pow (x : Fin n → ℝ)
    (p : CMvPolynomial n Rat) (k : Nat) :
    aeval x (p ^ k) = aeval x p ^ k := by
  simp [aeval]

@[simp] theorem aeval_C (x : Fin n → ℝ) (r : Rat) :
    aeval x (C r : CMvPolynomial n Rat) = (r : ℝ) := by
  simp [aeval]

@[simp] theorem aeval_X (x : Fin n → ℝ) (i : Fin n) :
    aeval x (X i : CMvPolynomial n Rat) = x i := by
  simp [aeval]

@[simp] theorem aeval_neg (x : Fin n → ℝ)
    (p : CMvPolynomial n Rat) :
    aeval x (-p) = -aeval x p := by
  simp [aeval]

@[simp] theorem aeval_sub (x : Fin n → ℝ)
    (p q : CMvPolynomial n Rat) :
    aeval x (p - q) = aeval x p - aeval x q := by
  simp [aeval]

end

end CPoly.CMvPolynomial

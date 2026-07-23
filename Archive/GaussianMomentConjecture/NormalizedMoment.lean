/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.IntegralRelations
import Mathlib

set_option linter.minImports true

/-!
# Integral normalization of a Wick-moment relation

Fix a lower balanced height `A0`.  Each balanced Wick channel of height `A`
is divided by the common factorial `A0!`, leaving the integral coefficient

`multinomial * (A! / A0!)`.

Under the height-floor hypothesis `A0 ≤ A`, multiplication by `A0!` recovers
the raw integral Wick-moment relation exactly.  Over `ℂ`, where `A0!` is
nonzero, a vanishing raw Gaussian moment therefore forces the normalized
integral relation to vanish as well.
-/

open MvPolynomial Finset

namespace GMC2.NormalizedMoment

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- The factorial quotient attached to a channel of height `A`, normalized
at the common lower height `A0`. -/
def normalizedFactorial (A0 A : ℕ) : ℕ :=
  Nat.factorial A / Nat.factorial A0

/-- The accumulated Wick height of an indexed channel. -/
noncomputable def channelHeight (exponent : ι → Fin 2 →₀ ℕ)
    (r : ι → ℕ) : ℕ :=
  (GMC2.MomentRelations.channelExponent exponent r) 0

/-- The exact balance predicate for an indexed Wick channel. -/
noncomputable def IsBalanced (exponent : ι → Fin 2 →₀ ℕ)
    (r : ι → ℕ) : Prop :=
  (GMC2.MomentRelations.channelExponent exponent r) 0 =
    (GMC2.MomentRelations.channelExponent exponent r) 1

/-- Balance is an equality of natural exponents, hence decidable. -/
noncomputable instance instDecidableIsBalanced
    (exponent : ι → Fin 2 →₀ ℕ) (r : ι → ℕ) :
    Decidable (IsBalanced exponent r) :=
  Classical.propDecidable _

/-- Integral normalized Wick-moment polynomial.  Its balanced channel of
height `A` has coefficient `multinomial * (A! / A0!)`. -/
noncomputable def normalizedMomentRelationInt
    (exponent : ι → Fin 2 →₀ ℕ) (m A0 : ℕ) : MvPolynomial ι ℤ :=
  by
    classical
    exact
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        if IsBalanced exponent r then
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm r)
            ((Nat.multinomial Finset.univ r : ℤ) *
              normalizedFactorial A0 (channelHeight exponent r))
        else 0

/-- Evaluation formula for the normalized relation in an arbitrary
commutative `ℤ`-algebra. -/
theorem aeval_normalizedMomentRelationInt
    [CommRing R] [Algebra ℤ R]
    (exponent : ι → Fin 2 →₀ ℕ) (c : ι → R) (m A0 : ℕ) :
    MvPolynomial.aeval c (normalizedMomentRelationInt exponent m A0) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
        if IsBalanced exponent r then
          (Nat.multinomial Finset.univ r : R) *
            (∏ i, c i ^ r i) *
              (normalizedFactorial A0 (channelHeight exponent r) : R)
        else 0 := by
  classical
  simp only [normalizedMomentRelationInt, map_sum, MvPolynomial.aeval_def]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hbalanced
  · simp only [eval₂_monomial, map_mul, map_natCast]
    rw [Finsupp.prod_fintype]
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      ring
    · intro i
      simp
  · simp

/-- Exact arithmetic behind the normalization: whenever `A0 ≤ A`, the
factorial quotient is integral and multiplication by `A0!` recovers `A!`. -/
theorem factorial_mul_normalizedFactorial {A0 A : ℕ} (h : A0 ≤ A) :
    Nat.factorial A0 * normalizedFactorial A0 A = Nat.factorial A := by
  unfold normalizedFactorial
  exact Nat.mul_div_cancel' (Nat.factorial_dvd_factorial h)

/-- Raw-moment factorization in any commutative `ℤ`-algebra.  The only
hypothesis is the common lower bound on the heights of balanced mass-`m`
channels. -/
theorem factorial_mul_aeval_normalized_eq_aeval_momentRelationInt
    [CommRing R] [Algebra ℤ R]
    (exponent : ι → Fin 2 →₀ ℕ) (c : ι → R) (m A0 : ℕ)
    (hmin : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
      IsBalanced exponent r → A0 ≤ channelHeight exponent r) :
    (Nat.factorial A0 : R) *
        MvPolynomial.aeval c (normalizedMomentRelationInt exponent m A0) =
      MvPolynomial.aeval c
        (GMC2.IntegralRelations.momentRelationInt exponent m) := by
  rw [aeval_normalizedMomentRelationInt]
  rw [GMC2.IntegralRelations.aeval_momentRelationInt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hbalanced : IsBalanced exponent r
  · have hfloor := hmin r hr hbalanced
    have hfacNat := factorial_mul_normalizedFactorial hfloor
    have hfacR :
        (Nat.factorial A0 : R) *
            (normalizedFactorial A0 (channelHeight exponent r) : R) =
          (Nat.factorial (channelHeight exponent r) : R) := by
      have hcast := congrArg (fun n : ℕ => (n : R)) hfacNat
      simpa only [Nat.cast_mul] using hcast
    simp only [if_pos hbalanced]
    unfold IsBalanced at hbalanced
    unfold channelHeight at hfacR ⊢
    rw [if_pos hbalanced]
    calc
      (Nat.factorial A0 : R) *
          ((Nat.multinomial Finset.univ r : R) * (∏ i, c i ^ r i) *
            (normalizedFactorial A0
              ((GMC2.MomentRelations.channelExponent exponent r) 0) : R)) =
          (Nat.multinomial Finset.univ r : R) * (∏ i, c i ^ r i) *
            ((Nat.factorial A0 : R) *
              (normalizedFactorial A0
                ((GMC2.MomentRelations.channelExponent exponent r) 0) : R)) := by
            ring
      _ = (Nat.multinomial Finset.univ r : R) * (∏ i, c i ^ r i) *
            (Nat.factorial
              ((GMC2.MomentRelations.channelExponent exponent r) 0) : R) := by
            rw [hfacR]
  · simp only [if_neg hbalanced, mul_zero]
    unfold IsBalanced at hbalanced
    rw [if_neg hbalanced]

/-- Equivalent complex factorization with the raw Gaussian moment on the
right-hand side. -/
theorem factorial_mul_aeval_normalized_eq_E
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → ℂ) (m A0 : ℕ)
    (hmin : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
      IsBalanced exponent r → A0 ≤ channelHeight exponent r) :
    (Nat.factorial A0 : ℂ) *
        MvPolynomial.aeval coefficient
          (normalizedMomentRelationInt exponent m A0) =
      GMC2.E
        ((GMC2.MomentTransport.indexedPolynomial exponent coefficient) ^ m) := by
  rw [factorial_mul_aeval_normalized_eq_aeval_momentRelationInt
    exponent coefficient m A0 hmin]
  exact
    (GMC2.IntegralRelations.E_indexedPolynomial_pow_eq_aeval_momentRelationInt
      exponent coefficient m).symm

/-- Complex cancellation layer: if every balanced mass-`m` channel has
height at least `A0` and the raw Wick moment vanishes, then the normalized
integral moment polynomial also vanishes at the same coefficients. -/
theorem aeval_normalized_eq_zero_of_E_pow_eq_zero
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → ℂ) (m A0 : ℕ)
    (hmin : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m,
      IsBalanced exponent r → A0 ≤ channelHeight exponent r)
    (hraw : GMC2.E
      ((GMC2.MomentTransport.indexedPolynomial exponent coefficient) ^ m) = 0) :
    MvPolynomial.aeval coefficient
      (normalizedMomentRelationInt exponent m A0) = 0 := by
  have hfactor := factorial_mul_aeval_normalized_eq_E
    exponent coefficient m A0 hmin
  rw [hraw] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (by
    exact_mod_cast Nat.factorial_ne_zero A0)

end GMC2.NormalizedMoment


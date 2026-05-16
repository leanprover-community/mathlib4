/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Polynomial
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Sequences of binomial type

A sequence `p : ℕ → R[X]` is of **binomial type** if the coalgebra comultiplication
satisfies the binomial convolution formula:

  `Δ(pₙ) = Σ_{k=0}^{n} C(n,k) • (pₖ ⊗ pₙ₋ₖ)`

This definition captures polynomials whose behaviour under `x ↦ x + x'` factors through
binomial coefficients. The canonical examples are:
* the monomials `X ^ n` (the classical binomial theorem)
* the falling factorials `(x)_n = x(x-1)⋯(x-n+1)` (Vandermonde's identity)

## Main definitions

* `Polynomial.IsBinomialType`: predicate for a sequence satisfying the binomial convolution.

## Main results

* `Polynomial.X_pow_isBinomialType`: the monomial sequence is of binomial type.
* `Polynomial.descPochhammer_isBinomialType`: the falling factorial sequence is of binomial
  type (Vandermonde's identity).

## References

* Langer, R., *Macdonald Polynomials and Symmetric Functions*, arXiv:0907.3950, §1.2.2
* Roman, S., *The Umbral Calculus*, Academic Press, 1984
-/

public section

noncomputable section

open Polynomial TensorProduct Finset

open scoped TensorProduct

namespace Polynomial

variable (R : Type*) [CommSemiring R]

/-- A sequence `p : ℕ → R[X]` is of **binomial type** if
`Δ(pₙ) = Σ_{k=0}^{n} C(n,k) • (pₖ ⊗ pₙ₋ₖ)` where `Δ` is the additive group scheme
comultiplication on `R[X]`. -/
abbrev IsBinomialType (p : ℕ → R[X]) : Prop :=
  ∀ n, CoalgebraStruct.comul (p n) =
    (Finset.range (n + 1)).sum fun k =>
      (Nat.choose n k) • ((p k) ⊗ₜ[R] (p (n - k)))

/-- The monomial sequence `n ↦ X ^ n` is of binomial type.
This is the binomial theorem `(x + x')ⁿ = Σ C(n,k) xᵏ x'^{n-k}` expressed
coalgebraically. -/
theorem X_pow_isBinomialType : IsBinomialType R (fun n => (X : R[X]) ^ n) := by
  unfold IsBinomialType
  intro n
  -- Δ(X^n) = Δ(X)^n = (X⊗1 + 1⊗X)^n  (Δ is an algebra hom)
  change comulAdditiveAlgHom R (X ^ n) = _
  rw [map_pow, comulAdditiveAlgHom_X]
  -- X⊗1 commutes with 1⊗X in the tensor product algebra
  have hc : Commute ((X : R[X]) ⊗ₜ[R] (1 : R[X])) ((1 : R[X]) ⊗ₜ[R] (X : R[X])) :=
    (Commute.one_right X).tmul (Commute.one_left X)
  rw [hc.add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Algebra.TensorProduct.tmul_pow, one_pow, mul_one, one_mul,
             Algebra.TensorProduct.tmul_mul_tmul]
  rw [mul_comm, ← nsmul_eq_mul]

/-! ### Basic properties of binomial type sequences -/

/-- The zeroth term of a binomial type sequence is group-like:
`Δ(p₀) = p₀ ⊗ p₀`. This says `p₀` is an idempotent under comultiplication. -/
theorem IsBinomialType.comul_zero {p : ℕ → R[X]} (hp : IsBinomialType R p) :
    CoalgebraStruct.comul (p 0) = p 0 ⊗ₜ[R] p 0 := by
  suffices CoalgebraStruct.comul (p 0) =
      (Finset.range 1).sum fun k => (Nat.choose 0 k) • (p k ⊗ₜ[R] p (0 - k)) from by
    simpa using this
  exact hp 0

/-! ### Coalgebra endomorphisms preserve binomial type

The key structural theorem connecting coalgebra morphisms to binomial type sequences:
if `φ` is a coalgebra endomorphism of `R[X]` and `{pₙ}` is binomial type, then
`{φ(pₙ)}` is binomial type. This is the abstract engine behind umbral operators. -/

/-- Coalgebra endomorphisms preserve binomial type sequences. If `φ : R[X] →ₗc[R] R[X]`
and `{pₙ}` is binomial type, then `{φ(pₙ)}` is binomial type. -/
theorem IsBinomialType.comp_coalgebraHom {p : ℕ → R[X]} (hp : IsBinomialType R p)
    (φ : R[X] →ₗc[R] R[X]) :
    IsBinomialType R (fun n => φ (p n)) := by
  suffices ∀ n, CoalgebraStruct.comul (φ.toLinearMap (p n)) =
      (Finset.range (n + 1)).sum fun k =>
        (Nat.choose n k) • (φ.toLinearMap (p k) ⊗ₜ[R] φ.toLinearMap (p (n - k))) from this
  intro n
  have key := (LinearMap.congr_fun φ.map_comp_comul (p n)).symm
  simp only [LinearMap.comp_apply] at key
  rw [key, hp n, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_nsmul, TensorProduct.map_tmul]

/-- For any coalgebra endomorphism `φ`, the sequence `n ↦ φ(Xⁿ)` is binomial type. -/
theorem IsBinomialType.of_coalgebraHom (φ : R[X] →ₗc[R] R[X]) :
    IsBinomialType R (fun n => φ ((X : R[X]) ^ n)) := by
  suffices ∀ n, CoalgebraStruct.comul (φ.toLinearMap (X ^ n)) =
      (Finset.range (n + 1)).sum fun k =>
        (Nat.choose n k) • (φ.toLinearMap ((X : R[X]) ^ k) ⊗ₜ[R]
          φ.toLinearMap ((X : R[X]) ^ (n - k))) from this
  intro n
  have key := (LinearMap.congr_fun φ.map_comp_comul (X ^ n)).symm
  simp only [LinearMap.comp_apply] at key
  rw [key, (X_pow_isBinomialType R) n, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_nsmul, TensorProduct.map_tmul]

end Polynomial

end

/-! ### Falling factorials (CommRing required) -/

public section

noncomputable section

open Polynomial TensorProduct Finset

open scoped TensorProduct

namespace Polynomial

variable (R : Type*) [CommRing R]

/-- The comultiplication of `X - ↑n` in the `𝔾ₐ` coalgebra on `R[X]`. -/
private theorem comul_X_sub_natCast (n : ℕ) :
    CoalgebraStruct.comul ((X : R[X]) - (↑n : R[X])) =
      ((X : R[X]) - (↑n : R[X])) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (X : R[X]) := by
  change comulAdditiveAlgHom R ((X : R[X]) - (↑n : R[X])) = _
  have hnat : (↑n : R[X]) = C (↑n : R) := by simp
  rw [hnat, map_sub, comulAdditiveAlgHom_X, comulAdditiveAlgHom_C, ← hnat, sub_tmul]
  abel

/-- Recurrence: `p_k * (X - ↑n) = p_{k+1} + (↑k - ↑n) * p_k`. -/
private theorem descPochhammer_mul_X_sub (k n : ℕ) :
    descPochhammer R k * ((X : R[X]) - (↑n : R[X])) =
      descPochhammer R (k + 1) + ((↑k : R[X]) - (↑n : R[X])) * descPochhammer R k := by
  have h : (X : R[X]) - (↑n : R[X]) =
      (X - (↑k : R[X])) + ((↑k : R[X]) - (↑n : R[X])) := by ring
  rw [h, mul_add, ← descPochhammer_succ_right]
  ring

/-- Recurrence: `p_m * X = p_{m+1} + ↑m * p_m`. -/
private theorem descPochhammer_mul_X (m : ℕ) :
    descPochhammer R m * (X : R[X]) =
      descPochhammer R (m + 1) + (↑m : R[X]) * descPochhammer R m := by
  have h : (X : R[X]) = (X - (↑m : R[X])) + (↑m : R[X]) := by ring
  rw [h, mul_add, ← descPochhammer_succ_right]
  ring

/-- Key summand identity: for x ≤ n, distributing `Δ(X - ↑n)` over a binomial-type
summand and applying the descPochhammer recurrence on both tensor factors
produces a clean pair of successor terms.

The cross-terms `(↑x - ↑n) * p_x ⊗ p_{n-x}` and `p_x ⊗ ↑(n-x) * p_{n-x}` cancel
because constant polynomials are R-scalars that move freely in `R[X] ⊗[R] R[X]`,
and `(↑x - ↑n) + ↑(n - x) = 0` in R when `x ≤ n`. -/
private theorem summand_identity (x n : ℕ) (hx : x ≤ n) :
    (descPochhammer R x * ((X : R[X]) - (↑n : R[X]))) ⊗ₜ[R]
        descPochhammer R (n - x) +
      descPochhammer R x ⊗ₜ[R]
        (descPochhammer R (n - x) * (X : R[X])) =
    descPochhammer R (x + 1) ⊗ₜ[R] descPochhammer R (n - x) +
      descPochhammer R x ⊗ₜ[R] descPochhammer R (n + 1 - x) := by
  rw [descPochhammer_mul_X_sub R, descPochhammer_mul_X R]
  rw [add_tmul, tmul_add]
  have hC : ∀ (m : ℕ), (↑m : R[X]) = C (↑m : R) := by intro m; simp
  have hnat_l : ((↑x : R[X]) - (↑n : R[X])) * descPochhammer R x =
      ((↑x : R) - (↑n : R)) • descPochhammer R x := by
    rw [hC x, hC n, ← map_sub, ← smul_eq_C_mul]
  have hnat_r : (↑(n - x) : R[X]) * descPochhammer R (n - x) =
      (↑(n - x) : R) • descPochhammer R (n - x) := by
    rw [hC (n - x), ← smul_eq_C_mul]
  rw [hnat_l, hnat_r, TensorProduct.smul_tmul]
  have h0 :
      descPochhammer R x ⊗ₜ[R]
          ((↑x - ↑n : R) • descPochhammer R (n - x)) +
        descPochhammer R x ⊗ₜ[R]
          ((↑(n - x) : R) • descPochhammer R (n - x)) = 0 := by
    rw [← tmul_add, ← add_smul]
    have : (↑x : R) - (↑n : R) + (↑(n - x) : R) = 0 := by
      rw [Nat.cast_sub hx]; ring
    rw [this, zero_smul, tmul_zero]
  have hB := eq_neg_of_add_eq_zero_left h0
  have hn : n - x + 1 = n + 1 - x := by omega
  rw [hB, hn]; abel

/-- The falling factorial sequence `descPochhammer R` is of binomial type.
This is Vandermonde's identity `(x+y)_n = Σ C(n,k) (x)_k (y)_{n-k}`
expressed coalgebraically. -/
theorem descPochhammer_isBinomialType :
    IsBinomialType R (fun n => descPochhammer R n) := by
  unfold IsBinomialType
  intro n
  induction n with
  | zero =>
    simp [descPochhammer_zero, Bialgebra.comul_one,
          Algebra.TensorProduct.one_def]
  | succ n ih =>
    dsimp only at ih ⊢
    rw [descPochhammer_succ_right, Bialgebra.comul_mul, ih,
        comul_X_sub_natCast R n]
    rw [Finset.sum_mul]
    simp_rw [smul_mul_assoc, mul_add,
             Algebra.TensorProduct.tmul_mul_tmul]
    simp only [mul_one]
    have h_summand := Finset.sum_congr rfl
      (fun x (hx : x ∈ range (n + 1)) => by
        have hle : x ≤ n :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        change n.choose x •
            ((descPochhammer R x * ((X : R[X]) - ↑n)) ⊗ₜ[R]
              descPochhammer R (n - x) +
            descPochhammer R x ⊗ₜ[R]
              (descPochhammer R (n - x) * X)) =
          n.choose x •
            (descPochhammer R (x + 1) ⊗ₜ[R]
              descPochhammer R (n - x) +
            descPochhammer R x ⊗ₜ[R]
              descPochhammer R (n + 1 - x))
        congr 1
        exact summand_identity R x n hle)
    rw [h_summand]
    have h_split2 : ∀ x, n.choose x •
        (descPochhammer R (x + 1) ⊗ₜ[R]
          descPochhammer R (n - x) +
         descPochhammer R x ⊗ₜ[R]
          descPochhammer R (n + 1 - x)) =
        n.choose x •
          (descPochhammer R (x + 1) ⊗ₜ[R]
            descPochhammer R (n - x)) +
        n.choose x •
          (descPochhammer R x ⊗ₜ[R]
            descPochhammer R (n + 1 - x)) :=
      fun x => smul_add _ _ _
    simp only [h_split2, Finset.sum_add_distrib]
    symm
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, one_smul,
               Nat.succ_sub_succ_eq_sub]
    simp_rw [Nat.choose_succ_succ', add_smul]
    rw [Finset.sum_add_distrib]
    rw [add_assoc]
    congr 1
    rw [Finset.sum_range_succ,
        show Nat.choose n (n + 1) = 0 from
          Nat.choose_eq_zero_of_lt (by omega),
        zero_smul, add_zero]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, one_smul,
               Nat.succ_sub_succ_eq_sub]

end Polynomial

end

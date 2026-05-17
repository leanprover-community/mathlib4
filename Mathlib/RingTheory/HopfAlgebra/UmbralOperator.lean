/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.RingTheory.HopfAlgebra.DeltaOperator
public import Mathlib.RingTheory.PowerSeries.Substitution


/-!
# Umbral operators via generating functions

Given a delta operator `Q` on `R[X]` (over a ℚ-algebra `R`), the **delta series**
`f = deltaSeriesOf Q` is the formal power series whose k-th coefficient is
`(Q(X^k)).eval 0 / k!`. This series has zero constant term and unit linear
coefficient, so Mathlib's `substInvOfIsUnit` provides its compositional inverse `g`.

The **umbral operator** associated to `Q` is the coalgebra endomorphism of `R[X]`
sending `X^n` to the basic sequence polynomial `pₙ`, which is recovered from `g`
via `(pₙ).coeff k = descFactorial(n, n-k) • coeff n (g^k)`.

## Main definitions

* `Polynomial.deltaSeriesOf`: the generating function of a delta operator
* `Polynomial.deltaSeriesInv`: compositional inverse of the delta series
* `Polynomial.umbralPoly`: the basic sequence polynomial from the compositional inverse

## Main results

* `Polynomial.deltaSeriesOf_constantCoeff`: constant term is zero
* `Polynomial.deltaSeriesOf_isUnit_coeff_one`: linear coefficient is a unit
* `Polynomial.deltaSeriesInv_right`: `f(g) = X` (right compositional inverse)
* `Polynomial.deltaSeriesInv_left`: `g(f) = X` (left compositional inverse)

## References

* Langer, R., *Determinantal bases and the symmetric group*, arXiv:0907.3950, §1.2.2
* Roman, S., *The Umbral Calculus*, Academic Press, 1984, Chapter 2
-/

noncomputable section

open Polynomial Finset
open scoped PowerSeries

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### Delta series of a delta operator

The delta series `f(t) = Σ (Q(X^k)).eval 0 / k! · t^k` encodes the delta operator `Q`
as a formal power series. The division by `k!` is the exponential normalization that
ensures the compositional inverse recovers the correct basic sequence.

Since `Q` kills constants, the constant term vanishes. Since `Q(X)` has unit constant
coefficient and `1! = 1`, the linear coefficient is a unit. -/

set_option linter.unusedSectionVars false in
/-- Evaluation at zero equals the constant coefficient. -/
private theorem eval_zero_eq_coeff_zero (p : R[X]) : p.eval 0 = p.coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp [eval_monomial, coeff_monomial]
    by_cases hn : n = 0 <;> simp [hn, zero_pow]

/-- The **delta series** of a delta operator `Q`: the formal power series with
`k`-th coefficient `(Q(X^k)).eval 0 / k!`. -/
def deltaSeriesOf (Q : R[X] →ₗ[R] R[X]) : R⟦X⟧ :=
  PowerSeries.mk fun k =>
    algebraMap ℚ R (1 / ↑(Nat.factorial k)) * (Q (X ^ k)).eval 0

@[simp]
theorem deltaSeriesOf_coeff (Q : R[X] →ₗ[R] R[X]) (k : ℕ) :
    PowerSeries.coeff k (deltaSeriesOf Q) =
      algebraMap ℚ R (1 / ↑(Nat.factorial k)) * (Q (X ^ k)).eval 0 := by
  simp [deltaSeriesOf, PowerSeries.coeff_mk]

/-- The constant term of the delta series vanishes because `Q` kills constants. -/
theorem deltaSeriesOf_constantCoeff {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    PowerSeries.constantCoeff (R := R) (deltaSeriesOf Q) = 0 := by
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, deltaSeriesOf,
    PowerSeries.coeff_mk, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, map_one, one_mul]
  rw [show (1 : R[X]) = C 1 from by simp]
  rw [hQ.kills_constants]; simp

/-- The linear coefficient of the delta series is a unit: it equals `(Q X).eval 0 =
(Q X).coeff 0`, which is a unit by the delta operator axiom. -/
theorem deltaSeriesOf_isUnit_coeff_one {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    IsUnit (PowerSeries.coeff 1 (deltaSeriesOf Q)) := by
  simp only [deltaSeriesOf, PowerSeries.coeff_mk, Nat.factorial_one,
    Nat.cast_one, div_one, map_one, one_mul, pow_one]
  rw [eval_zero_eq_coeff_zero]
  exact hQ.unit_leading

/-- The delta series has `HasSubst` (can be substituted into other power series). -/
theorem deltaSeriesOf_hasSubst {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    PowerSeries.HasSubst (deltaSeriesOf Q) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (deltaSeriesOf_constantCoeff hQ)

/-! ### Compositional inverse of the delta series

The compositional inverse `g = substInvOfIsUnit (deltaSeriesOf Q)` encodes the basic
sequence: the polynomial `pₙ` has coefficients extractable from the powers of `g`.

The key finiteness property is that `g` has order ≥ 1 (zero constant term), so `g^k`
has order ≥ k, meaning `coeff n (g^k) = 0` whenever `k > n`. -/

/-- The compositional inverse of the delta series of `Q`. -/
def deltaSeriesInv (Q : R[X] →ₗ[R] R[X]) (hQ : IsDeltaOperator Q) : R⟦X⟧ :=
  (deltaSeriesOf Q).substInvOfIsUnit (deltaSeriesOf_isUnit_coeff_one hQ)

theorem deltaSeriesInv_constantCoeff {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    PowerSeries.constantCoeff (deltaSeriesInv Q hQ) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

theorem deltaSeriesInv_hasSubst {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    PowerSeries.HasSubst (deltaSeriesInv Q hQ) :=
  PowerSeries.HasSubst.substInvOfIsUnit _ _

/-- The delta series composed with its inverse gives `X`: `f(g) = X`. -/
theorem deltaSeriesInv_right {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    PowerSeries.subst (deltaSeriesOf Q) (deltaSeriesInv Q hQ) = PowerSeries.X := by
  simp only [deltaSeriesInv]
  exact PowerSeries.subst_substInvOfIsUnit_left (deltaSeriesOf Q)
    (deltaSeriesOf_constantCoeff hQ) (deltaSeriesOf_isUnit_coeff_one hQ)

/-- The inverse composed with the delta series gives `X`: `g(f) = X`. -/
theorem deltaSeriesInv_left {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    PowerSeries.subst (deltaSeriesInv Q hQ) (deltaSeriesOf Q) = PowerSeries.X := by
  simp only [deltaSeriesInv]
  exact PowerSeries.subst_substInvOfIsUnit_right (deltaSeriesOf Q)
    (deltaSeriesOf_constantCoeff hQ) (deltaSeriesOf_isUnit_coeff_one hQ)

/-! ### Umbral polynomials

The **umbral polynomial** `pₙ` is the basic sequence element recovered from the
compositional inverse `g`. The formula is:

  `(pₙ).coeff k = descFactorial(n, n-k) • coeff n (g^k)`

This is finite because `g` has order ≥ 1, so `g^k` has order ≥ k, forcing
`coeff n (g^k) = 0` for `k > n`. The polynomial has degree exactly `n`:
the leading coefficient comes from `coeff n (g^n) = (coeff 1 g)^n`, which is
a unit (since `g` is itself a delta series). -/

/-- The **umbral polynomial** `pₙ` associated to a delta operator `Q`.
Its `k`-th coefficient is `descFactorial(n, n-k) • coeff n (g^k)` where `g` is the
compositional inverse of the delta series. -/
def umbralPoly (Q : R[X] →ₗ[R] R[X]) (hQ : IsDeltaOperator Q) (n : ℕ) : R[X] :=
  (Finset.range (n + 1)).sum fun k =>
    C (↑(Nat.descFactorial n (n - k)) * PowerSeries.coeff n (deltaSeriesInv Q hQ ^ k)) *
      X ^ k

/-! ### Basic sequence properties of umbral polynomials -/

/-- The zeroth umbral polynomial is `1`. -/
theorem umbralPoly_zero {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    umbralPoly Q hQ 0 = 1 := by
  simp [umbralPoly, Finset.sum_range_one, Nat.descFactorial, pow_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]

/-- The umbral polynomials vanish at zero for `n ≥ 1`. -/
theorem umbralPoly_eval_zero {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) {n : ℕ}
    (hn : 0 < n) : (umbralPoly Q hQ n).eval 0 = 0 := by
  simp only [umbralPoly, Polynomial.eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases hk0 : k = 0
  · subst hk0; simp [PowerSeries.coeff_one, Nat.ne_of_gt hn]
  · simp [zero_pow hk0]

/-- The key power series identity: from `f(g) = X`, multiplying by `g^m` and
extracting `coeff (n+1)` gives `Σ_d (coeff d f) * coeff(n+1)(g^{d+m}) = coeff n (g^m)`.

Proof: rewrite g^{d+m} = g^d * g^m, expand via coeff_mul, swap the range/antidiagonal
sums, recognize the inner sum as coeff_i(subst f g) = coeff_i(X) via coeff_subst' + hfg,
collapse the antidiagonal to the single term i=1, and apply PowerSeries.coeff_succ_X_mul.

The Lean formalization requires careful handling of finsum ↔ Finset.sum conversion
(via `finsum_eq_sum_of_support_subset` with the order argument
`PowerSeries.le_order_pow_of_constantCoeff_eq_zero`). -/
private theorem inner_sum_eq {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    {i n : ℕ} (hi : i ≤ n + 1) :
    (Finset.range (n + 2)).sum (fun d =>
      PowerSeries.coeff d (deltaSeriesOf Q) *
        PowerSeries.coeff i (deltaSeriesInv Q hQ ^ d)) =
    PowerSeries.coeff i PowerSeries.X := by
  have hg0 := deltaSeriesInv_constantCoeff hQ
  have hg := deltaSeriesInv_hasSubst hQ
  have hleft := deltaSeriesInv_left hQ
  have hkey : PowerSeries.coeff i PowerSeries.X =
      ∑ᶠ d, PowerSeries.coeff d (deltaSeriesOf Q) *
        PowerSeries.coeff i (deltaSeriesInv Q hQ ^ d) := by
    have h := PowerSeries.coeff_subst' hg (deltaSeriesOf Q) i
    simp only [smul_eq_mul, hleft] at h; exact h
  rw [hkey]; symm
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hle; push_neg at hle
  exact hd (mul_eq_zero_of_right _ (PowerSeries.coeff_of_lt_order _
    (lt_of_lt_of_le (Nat.cast_lt.mpr (by omega : i < d))
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0))))

set_option maxHeartbeats 800000 in
private theorem key_coeff_identity {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (m n : ℕ) :
    (Finset.range (n + 2)).sum (fun d =>
      PowerSeries.coeff d (deltaSeriesOf Q) *
        PowerSeries.coeff (n + 1) (deltaSeriesInv Q hQ ^ (d + m))) =
    PowerSeries.coeff n (deltaSeriesInv Q hQ ^ m) := by
  set g := deltaSeriesInv Q hQ
  have hexp : ∀ d, PowerSeries.coeff (n + 1) (g ^ (d + m)) =
      (Finset.antidiagonal (n + 1)).sum (fun p =>
        PowerSeries.coeff p.1 (g ^ d) * PowerSeries.coeff p.2 (g ^ m)) := by
    intro d; rw [pow_add]; exact PowerSeries.coeff_mul ..
  simp_rw [hexp, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have goal_eq : (Finset.antidiagonal (n + 1)).sum (fun p =>
      (Finset.range (n + 2)).sum (fun d =>
        PowerSeries.coeff d (deltaSeriesOf Q) * PowerSeries.coeff p.1 (g ^ d)) *
      PowerSeries.coeff p.2 (g ^ m)) =
    (Finset.antidiagonal (n + 1)).sum (fun p =>
      PowerSeries.coeff p.1 PowerSeries.X * PowerSeries.coeff p.2 (g ^ m)) := by
    apply Finset.sum_congr rfl; intro p hp
    congr 1
    exact inner_sum_eq hQ (by have := Finset.mem_antidiagonal.mp hp; omega)
  rw [goal_eq, ← PowerSeries.coeff_mul, PowerSeries.coeff_succ_X_mul]

/-! ### Jabotinsky duality

The **Jabotinsky identity** `Σ_j coeff_j(f^k) · coeff_n(g^j) = δ_{kn}` is the "connecting
lemma" that links the power series composition `f(g) = X` to the polynomial duality between
basic sequences. It arises from the product of the Jabotinsky matrices for `f` and `g`
being the identity — a direct consequence of `substAlgHom` being a ring homomorphism.

In the finite operator calculus, this identity underpins the **duality pairing**
`⟨h, p⟩ = [x⁰] h(D)[p(x)]` between `R⟦X⟧` (acting as differential operators) and `R[X]`.
Under this pairing, the basic sequence `{pₙ}` is dual to the powers `{fᵏ}` of the delta
series: `⟨fᵏ, pₙ⟩ = n! · δ_{kn}`. The lowering property `Q(pₙ₊₁) = (n+1)·pₙ` then
follows from Q's adjoint being multiplication by `f`, which is trivial since `Q = f(D)`. -/

/-- The **Jabotinsky identity**: the product of Jabotinsky matrices for compositional
inverses is the identity. If `f(g) = X`, then `Σ_j [y^j](f^k) · [y^n](g^j) = δ_{kn}`.

This is the "connecting lemma" that converts a power series composition into
a change-of-basis relation between basic sequences. -/
private theorem jabotinsky_identity {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    (k n : ℕ) :
    (Finset.range (n + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        PowerSeries.coeff n (deltaSeriesInv Q hQ ^ j)) =
    if n = k then 1 else 0 := by
  have hg := deltaSeriesInv_hasSubst hQ
  have hg0 := deltaSeriesInv_constantCoeff hQ
  -- f^k(g) = (f(g))^k = X^k via substAlgHom being a ring hom
  have hfkg : PowerSeries.subst (deltaSeriesInv Q hQ) (deltaSeriesOf Q ^ k) =
      PowerSeries.X ^ k := by
    rw [PowerSeries.subst_pow hg, deltaSeriesInv_left hQ]
  -- Suffices to show the sum equals coeff n (X^k)
  suffices h : (Finset.range (n + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        PowerSeries.coeff n (deltaSeriesInv Q hQ ^ j)) =
    PowerSeries.coeff n (PowerSeries.X ^ k : R⟦X⟧) by
    rw [h, PowerSeries.coeff_X_pow]
  -- Expand via coeff_subst': coeff n (f^k(g)) = ∑ᶠ coeff_d(f^k) * coeff_n(g^d)
  have hcs := PowerSeries.coeff_subst' hg (deltaSeriesOf Q ^ k) n
  simp only [smul_eq_mul] at hcs
  rw [hfkg] at hcs
  -- hcs : coeff n (X^k) = ∑ᶠ d, coeff d (f^k) * coeff n (g^d)
  -- Goal: Finset.sum = coeff n (X^k); rewrite using hcs
  rw [hcs]; symm
  -- Convert finsum to Finset.sum (coeff n (g^d) = 0 for d > n by order bound)
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hle; push_neg at hle
  exact hd (mul_eq_zero_of_right _ (PowerSeries.coeff_of_lt_order _
    (lt_of_lt_of_le (Nat.cast_lt.mpr (by omega : n < d))
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0))))

/-- Q's action on monomials at the coefficient level: `(Q(X^l)).coeff m = C(l,m) * c_{l-m}`
where `c_k = (Q(X^k)).eval 0`. This follows from shift-equivariance + `Polynomial.funext`:
the eval identity `(Q(X^l)).eval a = Σ_k C(l,k) * c_k * a^{l-k}` identifies Q(X^l)
as the polynomial with coefficient `C(l,m) * c_{l-m}` at position m. -/
private theorem Q_monomial_coeff {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    {l m : ℕ} (hm : m ≤ l) :
    (Q (X ^ l)).coeff m = ↑(Nat.choose l m) * (Q (X ^ (l - m))).eval 0 := by
  -- Step 1: Eval identity from shift-equivariance
  -- Q(X^l).eval a = Σ_k C(l,k) * (Q(X^k)).eval 0 * a^{l-k} for all a
  have heval : ∀ a : R, (Q (X ^ l)).eval a =
      (Finset.range (l + 1)).sum (fun k =>
        ↑(Nat.choose l k) * (Q (X ^ k)).eval 0 * a ^ (l - k)) := by
    intro a
    -- Shift-equivariance: Q(taylor_a(X^l)) = taylor_a(Q(X^l))
    have hse : Q (taylor a (X ^ l)) = taylor a (Q (X ^ l)) := by
      have h := hQ.shift_equivariant
      exact DFunLike.congr_fun (h a) (X ^ l)
    -- Therefore Q(X^l).eval a = Q(taylor_a(X^l)).eval 0
    have h1 : (Q (X ^ l)).eval a = (Q (taylor a (X ^ l))).eval 0 := by
      have h := congr_arg (Polynomial.eval 0) hse
      rw [taylor_eval, zero_add] at h; exact h.symm
    rw [h1]
    -- Decompose taylor_a(X^l) into monomials, apply Q linearly
    have hnd : natDegree (taylor a (X ^ l)) < l + 1 := by
      rw [natDegree_taylor]
      have h1 : natDegree (X ^ l : R[X]) ≤ l * natDegree (X : R[X]) := natDegree_pow_le
      have h2 : natDegree (X : R[X]) ≤ 1 := natDegree_X_le
      nlinarith
    conv_lhs => rw [as_sum_range' (taylor a (X ^ l)) (l + 1) hnd]
    rw [map_sum]; simp only [eval_finset_sum]
    apply Finset.sum_congr rfl; intro k _
    simp only [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul]
    rw [Q.map_smul, eval_smul, smul_eq_mul, taylor_coeff]
    -- (hasseDeriv k (X^l)).eval a = C(l,k) * a^{l-k}
    rw [show (X : R[X]) ^ l = monomial l 1 from by simp [monomial_one_right_eq_X_pow]]
    rw [hasseDeriv_monomial, eval_monomial, mul_one]; ring
  -- Step 2: Identify Q(X^l) via eval_determines
  have hpoly : Q (X ^ l) = (Finset.range (l + 1)).sum (fun k =>
      C (↑(Nat.choose l k) * (Q (X ^ k)).eval 0) * X ^ (l - k)) := by
    have hdiff : Q (X ^ l) - (Finset.range (l + 1)).sum (fun k =>
        C (↑(Nat.choose l k) * (Q (X ^ k)).eval 0) * X ^ (l - k)) = 0 := by
      apply eval_determines; intro a
      rw [eval_sub, sub_eq_zero, heval a, eval_finset_sum]
      apply Finset.sum_congr rfl; intro k _
      simp [eval_mul, eval_C, eval_pow, eval_X, mul_assoc]
    exact sub_eq_zero.mp hdiff
  -- Step 3: Extract coeff m from the polynomial identity
  conv_lhs => rw [hpoly]
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single (l - m)]
  · -- Main term (k = l-m): l-(l-m) = m, so if m=m is true
    rw [show l - (l - m) = m from Nat.sub_sub_self hm, if_pos rfl, mul_one,
        show Nat.choose l (l - m) = Nat.choose l m from Nat.choose_symm hm]
  · -- Other terms vanish: l-k ≠ m when k ≠ l-m
    intro k hk_mem hk
    have hk_lt := Finset.mem_range.mp hk_mem
    have hne : l - k ≠ m := fun h => hk (by omega)
    simp [hne, Ne.symm hne]
  · -- l-m ∈ range(l+1)
    intro h; exact absurd (Finset.mem_range.mpr (by omega : l - m < l + 1)) h

/-- Factorial identity: `descFact(n+1, n+1-l) * C(l,m) * (l-m)! = descFact(n+1, n+1-m)`
for `m ≤ l ≤ n+1`. This is `(n+1)!/l! · l!/(m!(l-m)!) · (l-m)! = (n+1)!/m!`.

The proof multiplies both sides by `m!` and uses:
- `choose_mul_factorial_mul_factorial`: `C(l,m) * m! * (l-m)! = l!`
- `factorial_mul_descFactorial`: `(n-k)! * descFact(n,k) = n!` -/
private theorem descFactorial_choose_factorial {n l m : ℕ} (hm : m ≤ l) (hl : l ≤ n + 1) :
    Nat.descFactorial (n + 1) (n + 1 - l) * Nat.choose l m * Nat.factorial (l - m) =
    Nat.descFactorial (n + 1) (n + 1 - m) := by
  -- Multiply both sides by m! to get (n+1)! on both sides
  have h1 : Nat.choose l m * Nat.factorial m * Nat.factorial (l - m) = Nat.factorial l :=
    Nat.choose_mul_factorial_mul_factorial hm
  have hl' : n + 1 - (n + 1 - l) = l := by omega
  have hm' : n + 1 - (n + 1 - m) = m := by omega
  have h2 : l.factorial * Nat.descFactorial (n + 1) (n + 1 - l) = Nat.factorial (n + 1) := by
    have := Nat.factorial_mul_descFactorial (show n + 1 - l ≤ n + 1 by omega)
    rwa [hl'] at this
  have h3 : m.factorial * Nat.descFactorial (n + 1) (n + 1 - m) = Nat.factorial (n + 1) := by
    have := Nat.factorial_mul_descFactorial (show n + 1 - m ≤ n + 1 by omega)
    rwa [hm'] at this
  nlinarith [Nat.factorial_pos l, Nat.factorial_pos m, Nat.factorial_pos (l - m)]

/-- Relates `(Q(X^k)).eval 0` to `deltaSeriesOf`: rearranging the defining equation. -/
private theorem Q_eval_zero_eq {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (k : ℕ) :
    (Q (X ^ k)).eval 0 =
      algebraMap ℚ R (↑(Nat.factorial k)) *
        PowerSeries.coeff k (deltaSeriesOf Q) := by
  have h := deltaSeriesOf_coeff Q k
  rw [h, ← mul_assoc, ← map_mul, show (↑(Nat.factorial k) : ℚ) * (1 / ↑(Nat.factorial k)) = 1
    from by field_simp, map_one, one_mul]

/-! ### Umbral duality

The **umbral pairing** between `R⟦X⟧` and `R[X]` is the bilinear form
`⟨h, p⟩ = Σ_k coeff_k(h) · k! · p.coeff k` (the "derivative pairing"). Under it:

* **Orthogonality**: `⟨f^k, pₙ⟩ = n! · δ_{kn}` (Jabotinsky + factorial cancellation).
* **Adjoint**: `⟨f^k, Q(X^l)⟩ = ⟨f^{k+1}, X^l⟩` (Q's adjoint is multiplication by f).
* **Non-degeneracy**: `⟨f^k, p⟩ = 0` for all k implies `p = 0` (upper-triangular + units).

Together these give the lowering property as a corollary:
`Q(pₙ₊₁) - (n+1)·pₙ` pairs to zero against all `f^k`, hence vanishes. -/

set_option linter.unusedSectionVars false in
/-- In a ℚ-algebra, the natural-number cast of any factorial is a unit. -/
private theorem isUnit_natCast_factorial (k : ℕ) : IsUnit ((↑(Nat.factorial k) : R)) := by
  rw [show (↑(Nat.factorial k) : R) = algebraMap ℚ R ↑(Nat.factorial k) from
    (map_natCast (algebraMap ℚ R) _).symm]
  exact (algebraMap ℚ R).isUnit_map
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)))

/-- The leading coefficient of `f^m` at position `m`: if `constantCoeff f = 0`, then
`coeff m (f^m) = (coeff 1 f)^m`. This is because `f = c₁·X + c₂·X² + ...` gives
`f^m = c₁^m · X^m + higher order terms`. -/
private theorem coeff_self_pow {f : R⟦X⟧} (hf0 : PowerSeries.constantCoeff f = 0) (m : ℕ) :
    PowerSeries.coeff m (f ^ m) = (PowerSeries.coeff 1 f) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_eq_single (m, 1)]
    · rw [ih]; ring
    · intro p hab hne
      simp only [Finset.mem_antidiagonal] at hab
      obtain ⟨a, b⟩ := p; simp only at hab hne
      by_cases hb0 : b = 0
      · subst hb0
        have hc : PowerSeries.coeff 0 f = 0 := by
          rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [hc]; ring
      · by_cases hb1 : b = 1
        · subst hb1; simp only [add_right_cancel_iff] at hab; subst hab; exact absurd rfl hne
        · have hale : a < m := by omega
          have hzero : PowerSeries.coeff a (f ^ m) = 0 := by
            apply PowerSeries.coeff_of_lt_order
            exact lt_of_lt_of_le (Nat.cast_lt.mpr hale)
              (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m hf0)
          rw [hzero, zero_mul]
    · intro h; exfalso; apply h; simp [Finset.mem_antidiagonal]

/-- Coefficient extraction from the umbral polynomial definition. -/
private theorem umbralPoly_coeff {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    {n j : ℕ} (hj : j ≤ n) :
    (umbralPoly Q hQ n).coeff j =
      ↑(Nat.descFactorial n (n - j)) * PowerSeries.coeff n (deltaSeriesInv Q hQ ^ j) := by
  simp only [umbralPoly, Polynomial.finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj; rw [if_neg (Ne.symm hkj)]; ring
  · intro h; exfalso; apply h; simp [Finset.mem_range]; omega

set_option maxHeartbeats 800000 in
/-- **Orthogonality**: the factorial-weighted pairing of `f^k` with `pₙ` equals `n! · δ_{kn}`.

Proof: substitute `umbralPoly_coeff`, use `j! · descFact(n, n-j) = n!` to factor out `n!`,
then apply `jabotinsky_identity`. -/
private theorem pairing_umbralPoly {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    (k n : ℕ) :
    (Finset.range (n + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        (↑(Nat.factorial j) : R) * (umbralPoly Q hQ n).coeff j) =
    if k = n then (↑(Nat.factorial n) : R) else 0 := by
  trans (Finset.range (n + 1)).sum (fun j =>
    PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
      (↑(Nat.factorial j) : R) *
        (↑(Nat.descFactorial n (n - j)) * PowerSeries.coeff n (deltaSeriesInv Q hQ ^ j)))
  · apply Finset.sum_congr rfl; intro j hj
    rw [umbralPoly_coeff hQ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  trans ((↑(Nat.factorial n) : R) * (Finset.range (n + 1)).sum (fun j =>
    PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
      PowerSeries.coeff n (deltaSeriesInv Q hQ ^ j)))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hfact : (j.factorial : R) * ↑(Nat.descFactorial n (n - j)) = ↑(n.factorial) := by
      have key : n - (n - j) = j := by omega
      have h : j.factorial * Nat.descFactorial n (n - j) = n.factorial := by
        have := Nat.factorial_mul_descFactorial (show n - j ≤ n by omega)
        rw [key] at this; exact this
      push_cast [← h]; ring
    rw [← hfact]; ring
  rw [jabotinsky_identity hQ k n]
  simp only [eq_comm (a := n) (b := k)]
  split_ifs with h
  · simp
  · simp

set_option maxHeartbeats 1200000 in
/-- **Adjoint on monomials**: the pairing of `f^k` with `Q(X^l)` equals `l! · coeff_l(f^{k+1})`.

This is the statement that Q's adjoint under the derivative pairing is multiplication by f.
Proof: apply `Q_monomial_coeff` + `Q_eval_zero_eq` to get `j! · C(l,j) · (l-j)! · coeff_{l-j}(f)`,
simplify `j! · C(l,j) · (l-j)! = l!`, factor out `l!`, recognize convolution as `coeff_l(f^{k+1})`. -/
private theorem pairing_Q_X_pow {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (k l : ℕ) :
    (Finset.range (l + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        (↑(Nat.factorial j) : R) * (Q (X ^ l)).coeff j) =
    (↑(Nat.factorial l) : R) * PowerSeries.coeff l (deltaSeriesOf Q ^ (k + 1)) := by
  trans (Finset.range (l + 1)).sum (fun j =>
    PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
      (↑(Nat.factorial j) : R) *
        (↑(Nat.choose l j) * (algebraMap ℚ R (↑(Nat.factorial (l - j))) *
          PowerSeries.coeff (l - j) (deltaSeriesOf Q))))
  · apply Finset.sum_congr rfl; intro j hj
    have hj' : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Q_monomial_coeff hQ hj', Q_eval_zero_eq hQ (l - j)]
  trans ((↑(Nat.factorial l) : R) * (Finset.range (l + 1)).sum (fun j =>
    PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
      PowerSeries.coeff (l - j) (deltaSeriesOf Q)))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    have hj' : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hfact : (j.factorial : R) * ↑(Nat.choose l j) * (algebraMap ℚ R (↑(Nat.factorial (l - j)))) = ↑(l.factorial) := by
      rw [map_natCast]
      have h := Nat.choose_mul_factorial_mul_factorial hj'
      push_cast [← h]; ring
    rw [← hfact]; ring
  congr 1
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [← Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
    PowerSeries.coeff a (deltaSeriesOf Q ^ k) * PowerSeries.coeff b (deltaSeriesOf Q))]

/-- Helper: if the pairing is zero and all higher coefficients vanish, then `p.coeff m' = 0`. -/
private lemma coeff_zero_of_pairing_zero {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    {p : R[X]} {N : ℕ}
    (hp : ∀ k ≤ N, (Finset.range (N + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        (↑(Nat.factorial j) : R) * p.coeff j) = 0)
    {m' : ℕ} (hm' : m' ≤ N)
    (higher_zero : ∀ j : ℕ, m' < j → j ≤ N → p.coeff j = 0) :
    p.coeff m' = 0 := by
  have h := hp m' hm'
  rw [Finset.sum_eq_single m'] at h
  · have hunit_coeff : IsUnit (PowerSeries.coeff m' (deltaSeriesOf Q ^ m')) := by
      rw [coeff_self_pow (deltaSeriesOf_constantCoeff hQ)]
      exact (deltaSeriesOf_isUnit_coeff_one hQ).pow m'
    have hunit : IsUnit (PowerSeries.coeff m' (deltaSeriesOf Q ^ m') * ↑m'.factorial) :=
      hunit_coeff.mul (isUnit_natCast_factorial m')
    exact hunit.mul_right_eq_zero.mp h
  · intro j hj hjm'
    simp only [Finset.mem_range] at hj
    by_cases hjlt : j < m'
    · have hzero : PowerSeries.coeff j (deltaSeriesOf Q ^ m') = 0 :=
        PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (Nat.cast_lt.mpr hjlt)
          (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m' (deltaSeriesOf_constantCoeff hQ)))
      simp [hzero]
    · simp [higher_zero j (by omega) (by omega)]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Non-degeneracy**: if a polynomial of degree ≤ N pairs to zero against all `f^k`
(for k = 0, ..., N), then it is the zero polynomial.

Proof by descending induction: `f^m` has order `m`, so pairing with `f^m` isolates
`coeff_m(f^m) · m! · p.coeff m` (all lower-j terms vanish by order, all higher-j terms
vanish by induction hypothesis). Since `coeff_m(f^m) = (coeff_1 f)^m` is a unit and
`m!` is a unit in a ℚ-algebra, we get `p.coeff m = 0`. -/
private theorem pairing_eq_zero_imp_eq_zero {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    {p : R[X]} {N : ℕ} (hdeg : p.natDegree ≤ N)
    (hp : ∀ k ≤ N, (Finset.range (N + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        (↑(Nat.factorial j) : R) * p.coeff j) = 0) :
    p = 0 := by
  ext m; simp only [Polynomial.coeff_zero]
  by_cases hm : N < m
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hm)
  · have hm_le : m ≤ N := by omega
    suffices key : ∀ d : ℕ, ∀ m' : ℕ, m' ≤ N → N - m' ≤ d → p.coeff m' = 0 by
      exact key (N - m) m hm_le (le_refl _)
    intro d; induction d with
    | zero =>
      intro m' hm' hdiff
      have hm'N : m' = N := by omega
      subst hm'N
      exact coeff_zero_of_pairing_zero hQ hp (le_refl _) (fun j hj hjN =>
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hj))
    | succ d ih =>
      intro m' hm' hdiff
      apply coeff_zero_of_pairing_zero hQ hp hm'
      intro j hjgt hjle
      apply ih j hjle; omega

/-- The degree of the umbral polynomial `pₙ` is at most `n`. -/
private theorem natDegree_umbralPoly_le {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (n : ℕ) :
    (umbralPoly Q hQ n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans hkn

/-- Helper: extend the pairing range for `Q(X^l)` from `range(l+1)` to `range(n+1)` when
`l ≤ n+1`, using the degree bound `natDegree_delta_op_pow`. -/
private lemma pairing_extend {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    (k l n : ℕ) (hln : l ≤ n + 1) :
    (Finset.range (n + 1)).sum (fun j =>
      PowerSeries.coeff j (deltaSeriesOf Q ^ k) *
        (↑(Nat.factorial j) : R) * (Q (X ^ l)).coeff j) =
    (↑(Nat.factorial l) : R) * PowerSeries.coeff l (deltaSeriesOf Q ^ (k + 1)) := by
  rw [← pairing_Q_X_pow hQ k l]
  by_cases hl0 : l = 0
  · subst hl0
    simp only [pow_zero, Finset.range_one]
    rw [show (1 : R[X]) = C 1 from by simp, hQ.kills_constants]
    simp
  · have hl1 : 0 < l := Nat.pos_of_ne_zero hl0
    have hzero : ∀ j : ℕ, l ≤ j → (Q (X ^ l)).coeff j = 0 := by
      intro j hj
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hd := natDegree_delta_op_pow hQ l (by omega)
      omega
    by_cases hln' : l ≤ n
    · apply (Finset.sum_subset (Finset.range_mono (by omega)) _).symm
      intro j hj hjl
      simp only [Finset.mem_range, not_lt] at hj hjl
      rw [hzero j (by linarith)]; ring
    · have heq : l = n + 1 := by omega
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjl
      simp only [Finset.mem_range, not_lt] at hj hjl
      rw [hzero j (by omega)]; ring

set_option maxHeartbeats 4000000 in
/-- The lowering property: `Q(pₙ₊₁) = (n+1) • pₙ`.

**Proof by umbral duality.** Under the derivative pairing `⟨h, p⟩ = Σ_k coeff_k(h)·k!·p.coeff k`:
1. `⟨f^k, Q(pₙ₊₁)⟩ = ⟨f^{k+1}, pₙ₊₁⟩ = (n+1)! · δ_{kn}` (adjoint + orthogonality)
2. `⟨f^k, (n+1)·pₙ⟩ = (n+1)·n! · δ_{kn} = (n+1)! · δ_{kn}` (orthogonality)
3. Their difference pairs to zero, so vanishes by non-degeneracy. -/
theorem umbralPoly_lowering {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (n : ℕ) :
    Q (umbralPoly Q hQ (n + 1)) = (n + 1) • umbralPoly Q hQ n := by
  set f := deltaSeriesOf Q
  set g := deltaSeriesInv Q hQ
  -- Strategy: show the difference pairs to zero against all f^k, then non-degeneracy
  suffices h : Q (umbralPoly Q hQ (n + 1)) - (n + 1) • umbralPoly Q hQ n = 0 from
    sub_eq_zero.mp h
  apply pairing_eq_zero_imp_eq_zero hQ (N := n)
  · -- Degree bound for the difference
    have hd1 : (Q (umbralPoly Q hQ (n + 1))).natDegree ≤ n := by
      -- Q(p_{n+1}) = Σ_k a_k • Q(X^k); each Q(X^k) has degree ≤ k-1 ≤ n
      simp only [umbralPoly]
      rw [map_sum]; simp_rw [← smul_eq_C_mul, map_smul]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      apply (Polynomial.natDegree_smul_le _ _).trans
      by_cases hk0 : k = 0
      · subst hk0
        have : Q (X ^ 0) = 0 := by
          rw [pow_zero, show (1 : R[X]) = C 1 from by simp]
          exact hQ.kills_constants 1
        rw [this]; exact Nat.zero_le _
      · have hkn : k < n + 2 := Finset.mem_range.mp hk
        exact (natDegree_delta_op_pow hQ k (by omega)).trans (by omega)
    have hd2 : ((n + 1) • umbralPoly Q hQ n).natDegree ≤ n :=
      (Polynomial.natDegree_smul_le _ _).trans (natDegree_umbralPoly_le hQ n)
    exact (Polynomial.natDegree_sub_le_of_le hd1 hd2).trans (by simp)
  · intro k hk
    -- Show the pairing of f^k with (Q(p_{n+1}) - (n+1)•p_n) is zero
    -- Split: pairing is linear
    have hlin : (Finset.range (n + 1)).sum (fun j =>
        PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) *
          (Q (umbralPoly Q hQ (n + 1)) - (n + 1) • umbralPoly Q hQ n).coeff j) =
      (Finset.range (n + 1)).sum (fun j =>
        PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) *
          (Q (umbralPoly Q hQ (n + 1))).coeff j) -
      (Finset.range (n + 1)).sum (fun j =>
        PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) *
          ((n + 1) • umbralPoly Q hQ n).coeff j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [Polynomial.coeff_sub]; ring
    rw [hlin]
    -- Part 2: pairing(f^k, (n+1)•p_n) = (n+1) * n! * δ_{kn} = (n+1)! * δ_{kn}
    have hpart2 : (Finset.range (n + 1)).sum (fun j =>
        PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) *
          ((n + 1) • umbralPoly Q hQ n).coeff j) =
      if k = n then (↑(Nat.factorial (n + 1)) : R) else 0 := by
      -- Pull out (n+1), apply pairing_umbralPoly, simplify (n+1)*n! = (n+1)!
      simp_rw [nsmul_eq_mul, Polynomial.coeff_natCast_mul]
      trans (↑(n + 1) * (Finset.range (n + 1)).sum (fun j =>
          PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) * (umbralPoly Q hQ n).coeff j))
      · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      rw [show (Finset.range (n + 1)).sum (fun j =>
          PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) * (umbralPoly Q hQ n).coeff j) =
        if k = n then (↑(Nat.factorial n) : R) else 0 from pairing_umbralPoly hQ k n]
      split_ifs with h
      · have h1 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
        push_cast [h1]; ring
      · ring
    -- Part 1: pairing(f^k, Q(p_{n+1})) = (n+1)! * δ_{kn}
    -- Strategy: expand by linearity, apply adjoint on each monomial, reassemble as
    -- pairing(f^{k+1}, p_{n+1}), then apply orthogonality
    have hpart1 : (Finset.range (n + 1)).sum (fun j =>
        PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) *
          (Q (umbralPoly Q hQ (n + 1))).coeff j) =
      if k = n then (↑(Nat.factorial (n + 1)) : R) else 0 := by
      -- Step 1: expand Q(p_{n+1}) by linearity and swap sums
      trans (Finset.range (n + 2)).sum (fun l =>
        (↑(Nat.descFactorial (n + 1) (n + 1 - l)) *
          PowerSeries.coeff (n + 1) (deltaSeriesInv Q hQ ^ l)) *
        (Finset.range (n + 1)).sum (fun j =>
          PowerSeries.coeff j (f ^ k) * ↑(Nat.factorial j) * (Q (X ^ l)).coeff j))
      · conv_lhs =>
          arg 2; ext j
          rw [umbralPoly, map_sum, Polynomial.finsetSum_coeff]
          simp only [map_smul, Polynomial.coeff_smul, ← smul_eq_C_mul, smul_eq_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro j _; ring
      -- Step 2: apply pairing_extend to each l-term
      trans (Finset.range (n + 2)).sum (fun l =>
        (↑(Nat.descFactorial (n + 1) (n + 1 - l)) *
          PowerSeries.coeff (n + 1) (deltaSeriesInv Q hQ ^ l)) *
        ((↑(Nat.factorial l) : R) * PowerSeries.coeff l (f ^ (k + 1))))
      · apply Finset.sum_congr rfl; intro l hl; congr 1
        exact pairing_extend hQ k l n (by simp [Finset.mem_range] at hl; omega)
      -- Step 3: reassemble as pairing(f^{k+1}, p_{n+1}) using umbralPoly_coeff
      trans (Finset.range (n + 2)).sum (fun l =>
        PowerSeries.coeff l (f ^ (k + 1)) * ↑(Nat.factorial l) *
          (umbralPoly Q hQ (n + 1)).coeff l)
      · apply Finset.sum_congr rfl; intro l hl
        have hlb : l ≤ n + 1 := by simp [Finset.mem_range] at hl; omega
        rw [umbralPoly_coeff hQ hlb]; ring
      -- Step 4: apply pairing_umbralPoly
      rw [pairing_umbralPoly hQ (k + 1) (n + 1)]
      simp only [Nat.add_right_cancel_iff]
    rw [hpart1, hpart2, sub_self]

/-- The umbral polynomial sequence forms a basic sequence for the delta operator `Q`. -/
theorem umbralPoly_isBasicSequence {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    IsBasicSequence Q (umbralPoly Q hQ) where
  lowering := umbralPoly_lowering hQ
  zero_one := umbralPoly_zero hQ
  normalized _ hn := umbralPoly_eval_zero hQ hn

/-! ### The umbral operator

The **umbral operator** is the linear map `R[X] →ₗ[R] R[X]` sending `X^n ↦ pₙ`
(extended by linearity). Once the lowering property is established, it becomes a
coalgebra homomorphism via `IsBasicSequence.isBinomialType`. -/

/-- The **umbral operator** associated to `Q`: the linear map sending each monomial
`X^n` to the corresponding umbral polynomial `pₙ`. -/
def umbralOp (Q : R[X] →ₗ[R] R[X]) (hQ : IsDeltaOperator Q) : R[X] →ₗ[R] R[X] :=
  Polynomial.lsum (fun n => LinearMap.lsmul R R[X] |>.flip (umbralPoly Q hQ n))

@[simp]
theorem umbralOp_monomial {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (n : ℕ) (a : R) :
    umbralOp Q hQ (monomial n a) = a • umbralPoly Q hQ n := by
  simp [umbralOp, Polynomial.lsum_apply, LinearMap.flip_apply, LinearMap.lsmul_apply,
    Polynomial.toFinsupp_monomial, Finsupp.sum_single_index]

theorem umbralOp_pow {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) (n : ℕ) :
    umbralOp Q hQ (X ^ n) = umbralPoly Q hQ n := by
  rw [show (X : R[X]) ^ n = monomial n 1 from by simp [monomial_one_right_eq_X_pow]]
  rw [umbralOp_monomial, one_smul]

end Polynomial

end

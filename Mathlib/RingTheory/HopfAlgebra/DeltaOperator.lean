/-
Copyright (c) 2025 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.RingTheory.HopfAlgebra.BinomialType
public import Mathlib.RingTheory.HopfAlgebra.Polynomial
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Polynomial.Basis

/-!
# Delta operators and basic sequences

A **delta operator** is a shift-equivariant linear operator on `R[X]` that kills
constants and sends `X` to a polynomial with unit constant term. The derivative
and forward difference operator are the canonical examples.

Each delta operator `Q` has a unique **basic sequence** `{pₙ}` satisfying
`Q(pₙ₊₁) = (n+1) • pₙ` with `p₀ = 1` and `pₙ(0) = 0` for `n ≥ 1`.
The fundamental theorem of the umbral calculus (Rota's classification) states
that these are exactly the sequences of binomial type.

## Main definitions

* `Polynomial.IsShiftEquivariant`: `Q` commutes with the Taylor shift `taylor a`
* `Polynomial.IsDeltaOperator`: shift-equivariant, kills constants, unit leading term
* `Polynomial.forwardDiff`: the forward difference operator `E_a - I`
* `Polynomial.IsBasicSequence`: the basic sequence of a delta operator

## Main results

* `Polynomial.hasseDeriv_isShiftEquivariant`: all Hasse derivatives are
  shift-equivariant
* `Polynomial.derivative_isDeltaOperator`: the derivative is a delta operator
* `Polynomial.forwardDiff_isDeltaOperator`: the forward difference is a delta
  operator
* `Polynomial.X_pow_isBasicSequence`: `{Xⁿ}` is the basic sequence of the
  derivative
* `Polynomial.descPochhammer_isBasicSequence_forwardDiff`: falling factorials are
  the basic sequence of the forward difference
* `Polynomial.IsBasicSequence.isBinomialType`: **Rota's classification** — basic
  sequences are of binomial type

## References

* Langer, R., *Macdonald Polynomials and Symmetric Functions*,
  arXiv:0907.3950, §1.2.2
* Roman, S., *The Umbral Calculus*, Academic Press, 1984
* Rota, G.-C., Kahaner, D., Odlyzko, A., *Finite Operator Calculus*,
  JMAA 42 (1973)
-/

public section

noncomputable section

open Polynomial Finset

namespace Polynomial

/-! ### Shift-equivariant operators

An operator `Q : R[X] →ₗ[R] R[X]` is shift-equivariant if it commutes with the
Taylor shift operator `taylor a` for all `a : R`. Equivalently, `Q` commutes
with the translation `p(x) ↦ p(x + a)`.

The Hasse derivatives `hasseDeriv k` are the prototypical shift-equivariant
operators. The proof uses the composition law
`hasseDeriv n ∘ hasseDeriv k = C(n+k,n) • hasseDeriv (n+k)` together with the
binomial symmetry `C(n+k,n) = C(n+k,k)`. -/

variable {R : Type*} [CommSemiring R]

/-- An operator `Q : R[X] →ₗ[R] R[X]` is shift-equivariant if it commutes with
the Taylor shift: `Q ∘ taylor a = taylor a ∘ Q` for all `a`. This means `Q`
respects the "addition of alphabets" structure underlying the coalgebra on
`R[X]`. -/
def IsShiftEquivariant (Q : R[X] →ₗ[R] R[X]) : Prop :=
  ∀ (a : R), Q.comp (taylor a) = (taylor a).comp Q

/-- Every Hasse derivative `hasseDeriv k` is shift-equivariant. -/
theorem hasseDeriv_isShiftEquivariant (k : ℕ) :
    IsShiftEquivariant (hasseDeriv k : R[X] →ₗ[R] R[X]) := by
  intro a
  apply LinearMap.ext; intro p
  apply Polynomial.ext; intro n
  simp only [LinearMap.comp_apply, hasseDeriv_coeff, taylor_coeff]
  rw [← LinearMap.comp_apply (hasseDeriv n) (hasseDeriv k),
      hasseDeriv_comp, LinearMap.smul_apply]
  rw [Polynomial.eval_smul, nsmul_eq_mul]
  congr 1
  exact congrArg (Nat.cast (R := R))
    (Nat.choose_symm_of_eq_add (show n + k = k + n by omega))

/-- Composition of shift-equivariant operators is shift-equivariant. -/
theorem isShiftEquivariant_comp {Q₁ Q₂ : R[X] →ₗ[R] R[X]}
    (h₁ : IsShiftEquivariant Q₁) (h₂ : IsShiftEquivariant Q₂) :
    IsShiftEquivariant (Q₁.comp Q₂) := by
  intro a
  rw [LinearMap.comp_assoc, h₂ a, ← LinearMap.comp_assoc,
      h₁ a, LinearMap.comp_assoc]

/-- The sum of shift-equivariant operators is shift-equivariant. -/
theorem isShiftEquivariant_add {Q₁ Q₂ : R[X] →ₗ[R] R[X]}
    (h₁ : IsShiftEquivariant Q₁) (h₂ : IsShiftEquivariant Q₂) :
    IsShiftEquivariant (Q₁ + Q₂) := by
  intro a
  simp only [LinearMap.add_comp, LinearMap.comp_add, h₁ a, h₂ a]

/-! ### Delta operators

A delta operator is a shift-equivariant operator that kills constants and
whose image of `X` has a unit constant term. The derivative `D` and the
forward difference `Δₐ = E_a - I` are the canonical examples. -/

/-- A **delta operator** on `R[X]` is a shift-equivariant linear operator that
kills constants and sends `X` to a polynomial with unit constant term. -/
structure IsDeltaOperator (Q : R[X] →ₗ[R] R[X]) : Prop where
  shift_equivariant : IsShiftEquivariant Q
  kills_constants : ∀ (r : R), Q (C r) = 0
  unit_leading : IsUnit ((Q X).coeff 0)

/-- The derivative (`hasseDeriv 1`) is a delta operator. -/
theorem derivative_isDeltaOperator :
    IsDeltaOperator (hasseDeriv 1 : R[X] →ₗ[R] R[X]) where
  shift_equivariant := hasseDeriv_isShiftEquivariant 1
  kills_constants r := by
    rw [hasseDeriv_one]; exact derivative_C
  unit_leading := by
    rw [hasseDeriv_one, derivative_X]
    simp [coeff_one]

end Polynomial

end -- end CommSemiring noncomputable section

/-! ### Forward difference operator (requires subtraction) -/

public section

noncomputable section

open Polynomial Finset TensorProduct

open scoped TensorProduct

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The forward difference operator `Δₐ = E_a - I`, where `E_a = taylor a`
is the shift operator. For `a = 1`, this sends `p(x) ↦ p(x + 1) - p(x)`. -/
def forwardDiff (a : R) : R[X] →ₗ[R] R[X] := taylor a - LinearMap.id

@[simp]
theorem forwardDiff_apply (a : R) (p : R[X]) :
    forwardDiff a p = taylor a p - p := by
  simp [forwardDiff]

theorem forwardDiff_X (a : R) : forwardDiff a (X : R[X]) = C a := by
  simp [forwardDiff, taylor_X]

theorem forwardDiff_C (a : R) (r : R) : forwardDiff a (C r) = 0 := by
  simp [forwardDiff, taylor_C]

/-- The forward difference operator `Δₐ` is shift-equivariant. -/
theorem forwardDiff_isShiftEquivariant (a : R) :
    IsShiftEquivariant (forwardDiff a) := by
  intro b
  apply LinearMap.ext; intro p
  simp only [LinearMap.comp_apply, forwardDiff_apply]
  rw [map_sub (taylor b)]
  congr 1
  rw [taylor_taylor, taylor_taylor, add_comm]

/-- The forward difference `Δₐ` is a delta operator when `a` is a unit. -/
theorem forwardDiff_isDeltaOperator (a : R) (ha : IsUnit a) :
    IsDeltaOperator (forwardDiff a) where
  shift_equivariant := forwardDiff_isShiftEquivariant a
  kills_constants := forwardDiff_C a
  unit_leading := by simp [coeff_C_zero, ha]

/-! ### Basic sequences

The basic sequence of a delta operator `Q` is the unique polynomial sequence
`{pₙ}` satisfying the lowering property `Q(pₙ₊₁) = (n+1) • pₙ`, normalized
by `p₀ = 1` and `pₙ(0) = 0` for `n ≥ 1`.

The fundamental theorem of the umbral calculus states that basic sequences are
exactly the sequences of binomial type. -/

/-- A sequence `p : ℕ → R[X]` is a **basic sequence** for an operator `Q` if:
* `Q(pₙ₊₁) = (n+1) • pₙ` (lowering property)
* `p₀ = 1`
* `pₙ(0) = 0` for `n ≥ 1` (normalization) -/
structure IsBasicSequence (Q : R[X] →ₗ[R] R[X]) (p : ℕ → R[X]) :
    Prop where
  lowering : ∀ n, Q (p (n + 1)) = (n + 1) • p n
  zero_one : p 0 = 1
  normalized : ∀ n, 0 < n → (p n).eval 0 = 0

/-- The monomial sequence `{Xⁿ}` is the basic sequence of the derivative.
The lowering property is `D(Xⁿ⁺¹) = (n+1) • Xⁿ` (the power rule). -/
theorem X_pow_isBasicSequence :
    IsBasicSequence (hasseDeriv 1 : R[X] →ₗ[R] R[X])
      (fun n => (X : R[X]) ^ n) where
  lowering n := by
    rw [hasseDeriv_one, derivative_pow_succ, derivative_X, mul_one]
    rw [nsmul_eq_mul, ← C_eq_natCast, Nat.cast_succ, map_add,
        map_one]
  zero_one := pow_zero X
  normalized n hn := by
    simp [eval_pow, eval_X, zero_pow (by omega : n ≠ 0)]

/-- Helper: `taylor 1` is multiplicative. -/
private theorem taylor_one_mul (f g : R[X]) :
    taylor 1 (f * g) = taylor 1 f * taylor 1 g := by
  change taylorAlgHom 1 (f * g) = taylorAlgHom 1 f * taylorAlgHom 1 g
  exact map_mul _ f g

/-- Helper: `taylor 1 (X - ↑(n+1)) = X - ↑n` in `R[X]`. -/
private theorem taylor_one_X_sub_natCast (n : ℕ) :
    taylor (1 : R) ((X : R[X]) - (↑(n + 1) : R[X])) =
      X - (↑n : R[X]) := by
  have : taylor (1 : R) (↑(n + 1) : R[X]) = (↑(n + 1) : R[X]) := by
    change taylorAlgHom 1 (↑(n + 1) : R[X]) = _
    exact map_natCast _ _
  rw [map_sub, taylor_X, this, Nat.cast_succ, C_1]
  ring

/-- The lowering property for falling factorials: `Δ₁(descPochhammer (n+1)) =
(n+1) • descPochhammer n`. -/
private theorem forwardDiff_one_descPochhammer (n : ℕ) :
    forwardDiff (1 : R) (descPochhammer R (n + 1)) =
      (n + 1) • descPochhammer R n := by
  induction n with
  | zero =>
    simp [descPochhammer_one, descPochhammer_zero,
          forwardDiff_apply, taylor_X, one_smul]
  | succ n ih =>
    rw [descPochhammer_succ_right, forwardDiff_apply,
        taylor_one_mul, taylor_one_X_sub_natCast]
    have ih' : taylor (1 : R) (descPochhammer R (n + 1)) =
        descPochhammer R (n + 1) +
          (n + 1) • descPochhammer R n := by
      calc taylor (1 : R) (descPochhammer R (n + 1))
          = forwardDiff (1 : R) (descPochhammer R (n + 1)) +
              descPochhammer R (n + 1) := by
            simp [forwardDiff_apply]
        _ = (n + 1) • descPochhammer R n +
              descPochhammer R (n + 1) := by rw [ih]
        _ = descPochhammer R (n + 1) +
              (n + 1) • descPochhammer R n := add_comm _ _
    rw [ih', add_mul, smul_mul_assoc, ← descPochhammer_succ_right]
    simp only [nsmul_eq_mul, Nat.cast_succ]
    ring

/-- The falling factorial sequence is the basic sequence of the forward
difference `Δ₁`. -/
theorem descPochhammer_isBasicSequence_forwardDiff :
    IsBasicSequence (forwardDiff (1 : R))
      (fun n => descPochhammer R n) where
  lowering := forwardDiff_one_descPochhammer
  zero_one := descPochhammer_zero R
  normalized n hn := by
    cases n with
    | zero => omega
    | succ n =>
      rw [descPochhammer_succ_left]
      simp [eval_mul, eval_X]

/-! ### Bridge to binomial type — Rota's classification

The fundamental theorem of the umbral calculus: the basic sequence of any delta
operator is a sequence of binomial type. This requires `Algebra ℚ R` because
the inductive step divides by `(k+1)` to extract binomial coefficients from a
recurrence.

The proof strategy:
1. Reduce the coproduct identity to a Taylor identity via `comul_taylor`
2. Prove the Taylor identity by induction using shift-equivariance + lowering
3. Lift back to the tensor product via `eval_tensor_zero` -/

variable [Algebra ℚ R]

/-! ### Helper lemmas for Rota's classification

Over a ℚ-algebra, polynomials that are invariant under all Taylor shifts must
be constants: the derivative is also shift-invariant and has lower degree, so
induction on `natDegree` terminates. From this we derive that delta operators
send X to a constant, reduce degree, and have trivial kernel (modulo
constants). -/

private theorem instTorsionFree : IsAddTorsionFree R :=
  IsAddTorsionFree.of_module_rat R

/-- A polynomial invariant under all Taylor shifts is constant. -/
private theorem taylor_invariant_eq_C (p : R[X])
    (h : ∀ a : R, taylor a p = p) : p = C (p.eval 0) := by
  suffices ∀ (d : ℕ) (q : R[X]), q.natDegree ≤ d →
      (∀ a, taylor a q = q) → q = C (q.eval 0) from
    this p.natDegree p le_rfl h
  intro d
  induction d with
  | zero =>
    intro q hd _
    rw [eq_C_of_natDegree_le_zero hd]
    simp [coeff_zero_eq_eval_zero]
  | succ n ih =>
    intro q hd hq
    have hq_der : ∀ a, taylor a (derivative q) = derivative q := by
      intro a
      have se := hasseDeriv_isShiftEquivariant (R := R) 1 a
      simp only [hasseDeriv_one] at se
      have h1 : derivative (taylor a q) =
          taylor a (derivative q) := by
        change (LinearMap.comp derivative (taylor a)) q =
          (LinearMap.comp (taylor a) derivative) q
        rw [se]
      rw [← h1, hq a]
    have hd_der : (derivative q).natDegree ≤ n := by
      have htf : IsAddTorsionFree R := instTorsionFree
      rw [← hasseDeriv_one, natDegree_hasseDeriv]; omega
    have hder_const := ih (derivative q) hd_der hq_der
    set c := (derivative q).eval 0
    have hcoeff : ∀ k, 1 ≤ k → q.coeff (k + 1) = 0 := by
      intro k hk
      have htf : IsAddTorsionFree R := instTorsionFree
      have h1 := congr_arg (fun p => coeff p k) hder_const
      simp only [coeff_derivative, coeff_C] at h1
      rw [if_neg (by omega)] at h1
      rw [show (↑k : R) + 1 = (↑(k + 1) : R) from by
        push_cast; ring] at h1
      rw [mul_comm, ← nsmul_eq_mul] at h1
      have h2 : (k + 1) • q.coeff (k + 1) =
          (k + 1) • (0 : R) := by rwa [smul_zero]
      exact htf.nsmul_right_injective (Nat.succ_ne_zero k) h2
    have q_form : q = C (q.coeff 0) + C (q.coeff 1) * X := by
      ext k
      match k with
      | 0 => simp
      | 1 => simp
      | k + 2 => simp [hcoeff (k + 1) (by omega)]
    have coeff1_zero : q.coeff 1 = 0 := by
      have h1 := congr_arg (Polynomial.eval 0) (hq 1)
      rw [taylor_eval, zero_add, q_form] at h1
      simp only [eval_add, eval_mul, eval_C, eval_X,
                 mul_zero, add_zero, mul_one] at h1
      exact add_left_cancel (h1.trans (add_zero _).symm)
    rw [coeff1_zero, C_0, zero_mul, add_zero] at q_form
    rw [q_form]; simp [coeff_zero_eq_eval_zero]

/-- For a delta operator, Q(X) is a constant polynomial with unit
constant term. -/
private theorem delta_op_Q_X_eq_C {Q : R[X] →ₗ[R] R[X]}
    (hQ : IsDeltaOperator Q) : Q X = C ((Q X).eval 0) := by
  apply taylor_invariant_eq_C
  intro a
  have se := hQ.shift_equivariant a
  have lhs : Q (taylor a X) = Q X := by
    rw [taylor_X]; simp [map_add, hQ.kills_constants]
  calc taylor a (Q X)
      = ((taylor a).comp Q) X := rfl
    _ = (Q.comp (taylor a)) X := by rw [← se]
    _ = Q (taylor a X) := rfl
    _ = Q X := lhs

/-- The coefficient of `X^{d-1}` in `taylor 1 g - g` equals
`↑d * leadingCoeff g`. -/
private theorem coeff_taylor_sub_eq (g : R[X])
    (hd : 2 ≤ g.natDegree) :
    (taylor 1 g - g).coeff (g.natDegree - 1) =
    ↑g.natDegree * g.leadingCoeff := by
  have htf : IsAddTorsionFree R := instTorsionFree
  rw [coeff_sub, taylor_coeff]
  set h := hasseDeriv (g.natDegree - 1) g
  have hnd : h.natDegree ≤ 1 := by
    calc h.natDegree =
        g.natDegree - (g.natDegree - 1) :=
          natDegree_hasseDeriv g _
      _ ≤ 1 := by omega
  have heval : h.eval 1 = h.coeff 0 + h.coeff 1 := by
    have hform : h = C (h.coeff 0) + C (h.coeff 1) * X := by
      ext k; match k with
      | 0 => simp
      | 1 => simp
      | k + 2 =>
        simp [coeff_eq_zero_of_natDegree_lt
          (by omega : h.natDegree < k + 2)]
    rw [hform]
    simp [eval_add, eval_mul, eval_C, eval_X]
  rw [heval]
  rw [show h.coeff 0 =
      ↑((0 + (g.natDegree - 1)).choose (g.natDegree - 1)) *
        g.coeff (0 + (g.natDegree - 1)) from
      hasseDeriv_coeff _ _ _,
      show h.coeff 1 =
      ↑((1 + (g.natDegree - 1)).choose (g.natDegree - 1)) *
        g.coeff (1 + (g.natDegree - 1)) from
      hasseDeriv_coeff _ _ _]
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    show 1 + (g.natDegree - 1) = g.natDegree from by omega,
    add_sub_cancel_left, leadingCoeff]
  congr 1; congr 1
  rw [show g.natDegree = g.natDegree - 1 + 1 from by omega]
  simp [Nat.choose_succ_self_right]

set_option linter.unusedSectionVars false in
/-- `Q` applied to a polynomial of degree `< N` gives degree `≤ N - 2`. -/
private theorem natDegree_Q_of_bounded
    {Q : R[X] →ₗ[R] R[X]} {p : R[X]} {N : ℕ}
    (hN : p.natDegree < N) (hN2 : 2 ≤ N)
    (hQ0 : ∀ r : R, Q (C r) = 0)
    (hQk : ∀ k, 1 ≤ k → k < N →
      (Q (X ^ k)).natDegree ≤ k - 1) :
    (Q p).natDegree ≤ N - 2 := by
  have hsum : Q p =
      (range N).sum (fun k => p.coeff k • Q (X ^ k)) := by
    conv_lhs => rw [as_sum_range' p N hN]
    rw [map_sum]; apply Finset.sum_congr rfl; intro k _
    simp only [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul]
    exact Q.map_smul _ _
  rw [hsum]
  exact natDegree_sum_le_of_forall_le (range N) _
    (fun k hk => by
      rw [Finset.mem_range] at hk
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · rw [pow_zero, show (1 : R[X]) = C 1 from by simp,
            hQ0, smul_zero, natDegree_zero]; omega
      · exact (natDegree_smul_le _ _).trans
          ((hQk k hk_pos hk).trans (by omega)))

/-- The degree of Q(X^n) is at most n-1 for delta operators over
ℚ-algebras. -/
private theorem natDegree_delta_op_pow
    {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q) :
    ∀ n, 1 ≤ n → (Q (X ^ n)).natDegree ≤ n - 1 := by
  suffices ∀ n, (∀ k, 1 ≤ k → k < n →
      (Q (X ^ k)).natDegree ≤ k - 1) →
      1 ≤ n → (Q (X ^ n)).natDegree ≤ n - 1 by
    intro n hn
    exact Nat.strongRecOn
      (motive := fun n =>
        1 ≤ n → (Q (X ^ n)).natDegree ≤ n - 1)
      n (fun n ih hn =>
        this n (fun k hk1 hkn => ih k hkn hk1) hn) hn
  intro n ih hn
  match n, hn with
  | 1, _ =>
    rw [pow_one, delta_op_Q_X_eq_C hQ, natDegree_C]
  | n + 2, _ =>
    set m := n + 2
    set g := Q (X ^ m)
    by_contra hbig; push Not at hbig
    have hg_ne : g ≠ 0 :=
      ne_zero_of_natDegree_gt (by omega)
    have htf : IsAddTorsionFree R := instTorsionFree
    have coeff_ne :
        (taylor 1 g - g).coeff (g.natDegree - 1) ≠ 0 := by
      rw [coeff_taylor_sub_eq g (by omega), ← nsmul_eq_mul]
      intro h
      exact leadingCoeff_ne_zero.mpr hg_ne
        (htf.nsmul_right_injective
          (by omega : g.natDegree ≠ 0)
          (by rwa [smul_zero] :
            g.natDegree • g.leadingCoeff =
              g.natDegree • 0))
    have hnd_lb :
        n + 1 ≤ (taylor 1 g - g).natDegree := by
      have := le_natDegree_of_ne_zero coeff_ne; omega
    have taylor_pow :
        taylor (1 : R) (X ^ m) = (X + C 1) ^ m := by
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [pow_succ, taylor_mul, ihm, taylor_X,
            pow_succ]
    have diff_eq :
        taylor 1 g - g = Q ((X + C 1) ^ m - X ^ m) := by
      have se := hQ.shift_equivariant 1
      have shift : taylor 1 g = Q ((X + C 1) ^ m) := by
        calc taylor 1 g
            = ((taylor 1).comp Q) (X ^ m) := rfl
          _ = (Q.comp (taylor 1)) (X ^ m) := by
              rw [← se]
          _ = Q (taylor 1 (X ^ m)) := rfl
          _ = Q ((X + C 1) ^ m) := by rw [taylor_pow]
      rw [shift, ← map_sub]
    haveI : Nontrivial R := by
      rcases subsingleton_or_nontrivial R with h | h
      · exfalso; haveI := h
        exact hg_ne (Subsingleton.eq_zero g)
      · exact h
    have hpm : ((X + C (1 : R)) ^ m).Monic :=
      (monic_X_add_C 1).pow m
    have hdp :
        ((X + C (1 : R)) ^ m).natDegree = m := by
      rw [(monic_X_add_C (1 : R)).natDegree_pow,
          natDegree_X_add_C, mul_one]
    have hnd_diff :
        (((X : R[X]) + C 1) ^ m - X ^ m).natDegree <
          m := by
      have hdeg := @degree_sub_lt R _
        ((X + C 1) ^ m) (X ^ m)
        (by rw [degree_eq_natDegree hpm.ne_zero,
              degree_eq_natDegree (monic_X_pow m).ne_zero,
              hdp, natDegree_X_pow])
        hpm.ne_zero
        (by rw [hpm.leadingCoeff,
              (monic_X_pow m).leadingCoeff])
      rw [degree_eq_natDegree hpm.ne_zero, hdp] at hdeg
      rcases eq_or_ne
        (((X : R[X]) + C 1) ^ m - X ^ m) 0 with
          h0 | hne
      · rw [h0, natDegree_zero]; omega
      · exact (natDegree_lt_iff_degree_lt hne).mpr hdeg
    have hnd_ub :
        (Q ((X + C 1) ^ m - X ^ m)).natDegree ≤ n := by
      have := natDegree_Q_of_bounded hnd_diff
        (by omega : 2 ≤ m) hQ.kills_constants
        (fun k hk1 hkm => ih k hk1 (by omega))
      omega
    rw [diff_eq] at hnd_lb; omega

set_option linter.unusedSectionVars false in
/-- Over a ℚ-algebra, `natDegree (taylor a p - p) ≤ natDegree p - 1`. -/
private theorem natDegree_taylor_sub_le (a : R) (p : R[X])
    (hp : 1 ≤ p.natDegree) :
    (taylor a p - p).natDegree ≤ p.natDegree - 1 := by
  by_contra h; push Not at h
  have hbound : (taylor a p - p).natDegree ≤ p.natDegree :=
    (natDegree_sub_le _ _).trans
      (by rw [natDegree_taylor, max_self])
  have heq :
      (taylor a p - p).natDegree = p.natDegree := by omega
  have hne : taylor a p - p ≠ 0 :=
    ne_zero_of_natDegree_gt (by omega)
  exact leadingCoeff_ne_zero.mpr hne (by
    rw [leadingCoeff, heq]
    simp [coeff_sub, coeff_taylor_natDegree])

/-- Over a ℚ-algebra, evaluation at all points determines the polynomial. -/
private theorem eval_determines (p : R[X])
    (h : ∀ a : R, p.eval a = 0) : p = 0 := by
  suffices ∀ n (q : R[X]), q.natDegree ≤ n →
      (∀ a, q.eval a = 0) → q = 0 from
    this p.natDegree p le_rfl h
  intro n; induction n with
  | zero =>
    intro q hd heval
    have hc := eq_C_of_natDegree_le_zero hd
    rw [hc] at heval ⊢
    simp only [eval_C] at heval
    rw [heval 0, C_0]
  | succ n ih =>
    intro q hd heval
    have htaylor_inv : ∀ a : R, taylor a q = q := by
      intro a
      rcases Nat.eq_zero_or_pos q.natDegree with
          hzero | hpos
      · rw [eq_C_of_natDegree_le_zero
            (by omega : q.natDegree ≤ 0), taylor_C]
      · have hfd_eval :
            ∀ b, (taylor a q - q).eval b = 0 := by
          intro b
          rw [eval_sub, taylor_eval]
          simp [heval]
        have hsmall :
            (taylor a q - q).natDegree ≤ n :=
          (natDegree_taylor_sub_le a q hpos).trans
            (by omega)
        have := ih (taylor a q - q) hsmall hfd_eval
        rwa [sub_eq_zero] at this
    rw [taylor_invariant_eq_C q htaylor_inv,
        heval 0, C_0]

/-- The expansion identity: if `Q(f) = 0`, then
`Σ cₖ • hasseDeriv k f = 0` where `cₖ = (Q(X^k)).eval 0`. -/
private theorem sum_hasseDeriv_eq_zero
    {Q : R[X] →ₗ[R] R[X]}
    (hse : ∀ a : R, Q.comp (taylor a) = (taylor a).comp Q)
    (_hkc : ∀ r : R, Q (C r) = 0)
    {f : R[X]} (hQf : Q f = 0) :
    (range (f.natDegree + 1)).sum
      (fun k => (Q (X ^ k)).eval 0 • hasseDeriv k f) =
        0 := by
  apply eval_determines; intro a
  simp only [eval_finsetSum, eval_smul, smul_eq_mul]
  have hQta : Q (taylor a f) = 0 := by
    have := congr_arg (· f) (hse a)
    simp only [LinearMap.comp_apply] at this
    rw [this, hQf]; simp
  have hdecomp : Q (taylor a f) =
      (range (f.natDegree + 1)).sum
        (fun k => (taylor a f).coeff k •
          Q (X ^ k)) := by
    conv_lhs =>
      rw [as_sum_range' (taylor a f) _
        (by rw [natDegree_taylor]
            exact Nat.lt_succ_of_le le_rfl)]
    rw [map_sum]; apply Finset.sum_congr rfl
    intro k _
    simp only [← C_mul_X_pow_eq_monomial,
               ← smul_eq_C_mul]
    exact Q.map_smul _ _
  have h0 :=
    congr_arg (Polynomial.eval 0) (hdecomp ▸ hQta)
  simp only [eval_finsetSum, eval_smul, smul_eq_mul,
             eval_zero] at h0
  convert h0 using 1; apply Finset.sum_congr rfl
  intro k _
  rw [taylor_coeff a f k]; ring

/-- If `Q(f) = 0` and `f.eval 0 = 0` for a delta operator over ℚ, then
`f = 0`. -/
private theorem delta_ker_eval_zero
    {Q : R[X] →ₗ[R] R[X]} (hQ : IsDeltaOperator Q)
    (f : R[X]) (hQf : Q f = 0) (hf0 : f.eval 0 = 0) :
    f = 0 := by
  by_contra hf_ne
  have htf : IsAddTorsionFree R := instTorsionFree
  have hd : 1 ≤ f.natDegree := by
    by_contra h
    have hc := eq_C_of_natDegree_le_zero
      (by omega : f.natDegree ≤ 0)
    rw [hc] at hf0 hf_ne
    simp only [eval_C] at hf0
    rw [hf0, C_0] at hf_ne; exact hf_ne rfl
  have hsum := sum_hasseDeriv_eq_zero
    hQ.shift_equivariant hQ.kills_constants hQf
  have hcoeff_sum : (range (f.natDegree + 1)).sum
      (fun k => ((Q (X ^ k)).eval 0 •
        hasseDeriv k f).coeff (f.natDegree - 1)) =
      0 := by
    have h := congr_arg
      (fun p => p.coeff (f.natDegree - 1)) hsum
    simp only [coeff_zero] at h; convert h using 1
    induction (range (f.natDegree + 1)) using
        Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      simp only [Finset.sum_cons, coeff_add]; rw [ih]
  simp only [coeff_smul, smul_eq_mul] at hcoeff_sum
  have hreduce := Finset.sum_eq_single 1
    (s := range (f.natDegree + 1))
    (f := fun k => (Q (X ^ k)).eval 0 *
      (hasseDeriv k f).coeff (f.natDegree - 1))
    (fun k hk hk1 => by
      dsimp only; rw [Finset.mem_range] at hk
      match k with
      | 0 =>
        rw [pow_zero,
            show (1 : R[X]) = C 1 from C_1.symm,
            hQ.kills_constants, eval_zero, zero_mul]
      | 1 => exact absurd rfl hk1
      | k + 2 =>
        rw [hasseDeriv_coeff,
            coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero, mul_zero])
    (fun h =>
      absurd (Finset.mem_range.mpr (by omega)) h)
  rw [hreduce] at hcoeff_sum; dsimp only at hcoeff_sum
  rw [pow_one, hasseDeriv_coeff,
      show f.natDegree - 1 + 1 = f.natDegree from
        by omega,
      Nat.choose_one_right] at hcoeff_sum
  have hc₁ : IsUnit ((Q X).eval 0) := by
    convert hQ.unit_leading using 1
    exact (coeff_zero_eq_eval_zero _).symm
  rcases hc₁ with ⟨u, hu⟩
  rw [← hu] at hcoeff_sum
  have h1 : (↑f.natDegree : R) * f.coeff f.natDegree =
      0 := (Units.mul_right_eq_zero u).mp hcoeff_sum
  rw [← nsmul_eq_mul] at h1
  have h2 : f.natDegree • f.coeff f.natDegree =
      f.natDegree • (0 : R) := by rwa [smul_zero]
  exact leadingCoeff_ne_zero.mpr hf_ne
    (htf.nsmul_right_injective
      (show f.natDegree ≠ 0 by omega) h2)

/-- The Taylor expansion of the basic sequence satisfies the binomial
identity. -/
private theorem taylor_basic_eq
    {Q : R[X] →ₗ[R] R[X]} {p : ℕ → R[X]}
    (hQ : IsDeltaOperator Q) (hp : IsBasicSequence Q p)
    (n : ℕ) (a : R) :
    taylor a (p n) = (Finset.range (n + 1)).sum fun k =>
      (Nat.choose n k) •
        (p k * C ((p (n - k)).eval a)) := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, zero_add, Nat.choose_zero_right,
      one_smul, Nat.sub_zero, hp.zero_one]
    rw [show (1 : R[X]) = C 1 from C_1.symm,
        taylor_C, eval_C, C_1, mul_one]
  | succ n ih =>
    suffices h : taylor a (p (n + 1)) -
        (Finset.range (n + 2)).sum (fun k =>
          (Nat.choose (n + 1) k) •
            (p k * C ((p (n + 1 - k)).eval a))) =
        0 from sub_eq_zero.mp h
    apply delta_ker_eval_zero hQ
    · -- Q(D) = 0
      rw [map_sub, sub_eq_zero]
      have hQ_lhs : Q (taylor a (p (n + 1))) =
          (n + 1) • taylor a (p n) := by
        have hse := congr_arg (· (p (n + 1)))
          (hQ.shift_equivariant a)
        simp only [LinearMap.comp_apply] at hse
        rw [hse, hp.lowering n, map_nsmul]
      have hQ_rhs : Q ((Finset.range (n + 2)).sum
          fun k => (n + 1).choose k •
            (p k * C (eval a (p (n + 1 - k))))) =
        (n + 1) • (Finset.range (n + 1)).sum fun k =>
          n.choose k •
            (p k * C (eval a (p (n - k)))) := by
        rw [map_sum]; simp_rw [map_nsmul]
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, one_smul,
          hp.zero_one, one_mul, hQ.kills_constants,
          add_zero]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [show n + 1 - (k + 1) = n - k from
          by omega]
        set r := eval a (p (n - k))
        rw [mul_comm (p (k + 1)) (C r),
            ← smul_eq_C_mul, Q.map_smul,
            hp.lowering k]
        rw [smul_comm r (k + 1 : ℕ) (p k),
            ← mul_smul,
            show (n + 1).choose (k + 1) * (k + 1) =
              (n + 1) * n.choose k from
              (Nat.add_one_mul_choose_eq n k).symm,
            mul_smul]
        congr 2; rw [smul_eq_C_mul, mul_comm]
      rw [hQ_lhs, hQ_rhs, ih]
    · -- D.eval 0 = 0
      rw [eval_sub, taylor_eval, zero_add,
          sub_eq_zero, eval_finsetSum]
      rw [Finset.sum_eq_single_of_mem 0
        (Finset.mem_range.mpr (by omega))]
      · simp [hp.zero_one, Nat.choose_zero_right]
      · intro k _ hk
        simp [hp.normalized k (by omega : 0 < k)]

set_option linter.unusedSectionVars false in
/-- The composition `lmul' ∘ (id ⊗ aeval(C a)) ∘ Δ` equals `taylor a`
as algebra homs. -/
private theorem comul_taylor_bridge (a : R) :
    (Algebra.TensorProduct.lmul' (R := R)
      (S := R[X])).comp
      ((Algebra.TensorProduct.map (AlgHom.id R R[X])
        (Polynomial.aeval (C a))).comp
       (Polynomial.comulAdditiveAlgHom R)) =
      Polynomial.taylorAlgHom a := by
  apply Polynomial.algHom_ext
  simp [comulAdditiveAlgHom_X,
        Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul,
        taylor_X]

set_option linter.unusedSectionVars false in
/-- `aeval (C a) g = C (g.eval a)`. -/
private theorem aeval_C_eq_C_eval (a : R)
    (g : R[X]) :
    Polynomial.aeval (C a) g = C (g.eval a) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n r =>
    rw [aeval_monomial, eval_monomial,
        ← C_eq_algebraMap, map_mul, map_pow]

/-- Tensor separation: if applying `lmul' ∘ (id ⊗ aeval(C a))` to `T`
gives `0` for all `a : R`, then `T = 0`. -/
private theorem eval_tensor_zero (T : R[X] ⊗[R] R[X])
    (h : ∀ a : R, (Algebra.TensorProduct.lmul' (R := R)
      (S := R[X]))
      ((Algebra.TensorProduct.map (AlgHom.id R R[X])
        (Polynomial.aeval (C a))) T) = 0) :
    T = 0 := by
  set e := TensorProduct.equivFinsuppOfBasisLeft
    (N := R[X]) (basisMonomials R) with he
  suffices e T = 0 by
    rwa [LinearEquiv.map_eq_zero_iff] at this
  apply Finsupp.ext; intro j
  simp only [Finsupp.zero_apply]
  apply eval_determines; intro a
  have key : ∀ (S : R[X] ⊗[R] R[X]),
      (e S j).eval a =
        ((Algebra.TensorProduct.lmul' (R := R)
          (S := R[X]))
          ((Algebra.TensorProduct.map
            (AlgHom.id R R[X])
            (aeval (C a))) S)).coeff j := by
    intro S
    induction S using TensorProduct.induction_on with
    | zero => simp [he, LinearEquiv.map_zero]
    | tmul f g =>
      simp only [he,
        equivFinsuppOfBasisLeft_apply_tmul_apply,
        Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul,
        aeval_C_eq_C_eval,
        eval_smul, smul_eq_mul, coeff_mul_C]
      rw [show ((basisMonomials R).repr f) j =
        f.coeff j from toFinsupp_apply f j]
    | add x y hx hy => simp [map_add, hx, hy]
  rw [key, h a, coeff_zero]

/-- **Rota's classification theorem** (umbral calculus): the basic sequence
of a delta operator is of binomial type. -/
theorem IsBasicSequence.isBinomialType
    {Q : R[X] →ₗ[R] R[X]} {p : ℕ → R[X]}
    (hQ : IsDeltaOperator Q) (hp : IsBasicSequence Q p) :
    IsBinomialType R p := by
  intro n
  rw [← sub_eq_zero]; apply eval_tensor_zero; intro a
  simp only [map_sub, sub_eq_zero, map_sum, map_nsmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.lmul'_apply_tmul,
    aeval_C_eq_C_eval]
  rw [show (Algebra.TensorProduct.lmul' (R := R)
      (S := R[X]))
      ((Algebra.TensorProduct.map (AlgHom.id R R[X])
        (aeval (C a)))
        (CoalgebraStruct.comul (p n))) =
      taylor a (p n) from by
    change _ = taylorAlgHom a (p n)
    exact AlgHom.congr_fun
      (comul_taylor_bridge a) (p n)]
  exact taylor_basic_eq hQ hp n a

end Polynomial

end

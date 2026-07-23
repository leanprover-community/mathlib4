/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Monic three-term recurrences and coprimality of consecutive members

A *monic three-term recurrence* over a commutative ring `R` is determined by two coefficient
sequences `a b : ℕ → R` and produces the monic polynomials
`p 0 = 1`, `p 1 = X - C (a 0)`, `p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n`.

This is the shape of every family of orthogonal polynomials — by Favard's theorem a sequence of
monic polynomials is orthogonal for some moment functional exactly when it satisfies such a
recurrence with `b n ≠ 0` — and also of Sturm sequences.

The main result `Polynomial.ThreeTermRecurrence.isCoprime_succ` says that when every off-diagonal
coefficient `b (n + 1)` is a unit, consecutive members `p n` and `p (n + 1)` are coprime. Over a
field this is the classical fact that consecutive orthogonal polynomials share no root, obtained
uniformly for Hermite, Legendre, Laguerre, Chebyshev, Gegenbauer, Jacobi, … . The proof is a single
Bézout update and uses no analysis and no estimates.

## Main definitions

* `Polynomial.ThreeTermRecurrence`: the coefficient data `a`, `b` of the recurrence.
* `Polynomial.ThreeTermRecurrence.p`: the resulting sequence of monic polynomials.
* `Polynomial.ThreeTermRecurrence.hermite`: the probabilists' Hermite recurrence, as an example.

## Main results

* `Polynomial.ThreeTermRecurrence.monic`, `Polynomial.ThreeTermRecurrence.natDegree_p`:
  `p n` is monic of degree `n`.
* `Polynomial.ThreeTermRecurrence.isCoprime_succ`: consecutive members are coprime, over any
  commutative ring, provided the off-diagonal coefficients are units.
* `Polynomial.ThreeTermRecurrence.isCoprime_succ_of_ne_zero`: the specialization to a field.
* `Polynomial.ThreeTermRecurrence.not_isRoot_and_isRoot_succ`: consecutive members share no root.
-/

@[expose] public section

namespace Polynomial

/-- Coefficient data of a monic three-term recurrence over a commutative ring `R`. -/
structure ThreeTermRecurrence (R : Type*) [CommRing R] where
  /-- The diagonal (recentring) coefficients. -/
  a : ℕ → R
  /-- The off-diagonal coefficients. The main results assume every `b (n + 1)` is a unit. -/
  b : ℕ → R

namespace ThreeTermRecurrence

variable {R : Type*} [CommRing R]

/-- The monic polynomial sequence attached to a three-term recurrence:
`p 0 = 1`, `p 1 = X - C (a 0)` and
`p (n + 2) = (X - C (a (n + 1))) * p (n + 1) - C (b (n + 1)) * p n`. -/
noncomputable def p (T : ThreeTermRecurrence R) : ℕ → R[X]
  | 0 => 1
  | 1 => X - C (T.a 0)
  | (n + 2) => (X - C (T.a (n + 1))) * p T (n + 1) - C (T.b (n + 1)) * p T n

variable (T : ThreeTermRecurrence R)

@[simp] theorem p_zero : T.p 0 = 1 := rfl

theorem p_one : T.p 1 = X - C (T.a 0) := rfl

theorem p_add_two (n : ℕ) :
    T.p (n + 2) = (X - C (T.a (n + 1))) * T.p (n + 1) - C (T.b (n + 1)) * T.p n := rfl

/-- Every member of the sequence is monic, of degree equal to its index. -/
theorem monic_and_natDegree [Nontrivial R] (n : ℕ) :
    (T.p n).Monic ∧ (T.p n).natDegree = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact ⟨monic_one, by simp⟩
    | 1 => exact ⟨monic_X_sub_C _, by rw [p_one, natDegree_X_sub_C]⟩
    | (k + 2) =>
      obtain ⟨hm1, hd1⟩ := ih (k + 1) (by omega)
      obtain ⟨_, hdk⟩ := ih k (by omega)
      have hA : ((X - C (T.a (k + 1))) * T.p (k + 1)).Monic := (monic_X_sub_C _).mul hm1
      have hAd : ((X - C (T.a (k + 1))) * T.p (k + 1)).natDegree = k + 2 := by
        rw [(monic_X_sub_C (T.a (k + 1))).natDegree_mul hm1, natDegree_X_sub_C, hd1]
        omega
      have hBk : (C (T.b (k + 1)) * T.p k).natDegree ≤ k :=
        le_trans (natDegree_C_mul_le _ _) hdk.le
      have hBlt : (C (T.b (k + 1)) * T.p k).degree
          < ((X - C (T.a (k + 1))) * T.p (k + 1)).degree := by
        rw [degree_eq_natDegree hA.ne_zero, hAd]
        calc (C (T.b (k + 1)) * T.p k).degree
            ≤ ((C (T.b (k + 1)) * T.p k).natDegree : WithBot ℕ) := degree_le_natDegree
          _ ≤ (k : WithBot ℕ) := by exact_mod_cast hBk
          _ < ((k + 2 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : k < k + 2)
      have hpe : T.p (k + 2)
          = (X - C (T.a (k + 1))) * T.p (k + 1) + -(C (T.b (k + 1)) * T.p k) := by
        rw [p_add_two]; ring
      refine ⟨?_, ?_⟩
      · rw [hpe]; exact hA.add_of_left (by rwa [degree_neg])
      · rw [hpe, natDegree_eq_of_degree_eq
            (degree_add_eq_left_of_degree_lt (by rwa [degree_neg])), hAd]

/-- Every member of the sequence is monic. -/
theorem monic [Nontrivial R] (n : ℕ) : (T.p n).Monic := (T.monic_and_natDegree n).1

/-- The `n`-th member of the sequence has degree `n`. -/
theorem natDegree_p [Nontrivial R] (n : ℕ) : (T.p n).natDegree = n := (T.monic_and_natDegree n).2

/-- **Consecutive members of a monic three-term recurrence are coprime**, provided every
off-diagonal coefficient `b (n + 1)` is a unit. This holds over an arbitrary commutative ring.

The proof is a single Bézout update: from `u * p n + v * p (n + 1) = 1` and
`p n = b⁻¹ * ((X - C a) * p (n + 1) - p (n + 2))` one reads off the Bézout witnesses
`(u * b⁻¹ * (X - C a) + v, -(u * b⁻¹))` for the pair `(p (n + 1), p (n + 2))`. -/
theorem isCoprime_succ (hb : ∀ n, IsUnit (T.b (n + 1))) :
    ∀ n, IsCoprime (T.p n) (T.p (n + 1)) := by
  intro n
  induction n with
  | zero => exact isCoprime_one_left
  | succ k ih =>
    obtain ⟨u, v, huv⟩ := ih
    have hCb : IsUnit (C (T.b (k + 1))) := isUnit_C.mpr (hb k)
    set binv := Ring.inverse (C (T.b (k + 1))) with hbdef
    have hbinv : binv * C (T.b (k + 1)) = 1 := Ring.inverse_mul_cancel _ hCb
    have hrec : T.p (k + 2)
        = (X - C (T.a (k + 1))) * T.p (k + 1) - C (T.b (k + 1)) * T.p k := rfl
    refine ⟨u * binv * (X - C (T.a (k + 1))) + v, -(u * binv), ?_⟩
    linear_combination (-(u * binv)) * hrec + huv + (u * T.p k) * hbinv

/-- Over a field it is enough that the off-diagonal coefficients are nonzero. -/
theorem isCoprime_succ_of_ne_zero {K : Type*} [Field K] (T : ThreeTermRecurrence K)
    (hb : ∀ n, T.b (n + 1) ≠ 0) (n : ℕ) : IsCoprime (T.p n) (T.p (n + 1)) :=
  T.isCoprime_succ (fun n => isUnit_iff_ne_zero.mpr (hb n)) n

/-- **Consecutive members of a monic three-term recurrence share no root.** This is the
evaluation-level consequence of `ThreeTermRecurrence.isCoprime_succ`. -/
theorem not_isRoot_and_isRoot_succ [Nontrivial R] (hb : ∀ n, IsUnit (T.b (n + 1))) (n : ℕ)
    (x : R) : ¬((T.p n).IsRoot x ∧ (T.p (n + 1)).IsRoot x) := by
  rintro ⟨h1, h2⟩
  have hco := (T.isCoprime_succ hb n).map (evalRingHom x)
  simp only [IsRoot.def] at h1 h2
  simp only [coe_evalRingHom, h1, h2] at hco
  exact not_isUnit_zero (isCoprime_zero_left.mp hco)

/-! ### The probabilists' Hermite polynomials as an example -/

/-- The probabilists' Hermite recurrence `Heₙ₊₂ = X * Heₙ₊₁ - (n + 1) * Heₙ`, as a
`ThreeTermRecurrence`: the diagonal coefficients vanish and `b n = n`. -/
noncomputable def hermite (K : Type*) [Field K] : ThreeTermRecurrence K where
  a := fun _ => 0
  b := fun n => (n : K)

theorem isUnit_hermite_b {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    IsUnit ((hermite K).b (n + 1)) :=
  isUnit_iff_ne_zero.mpr
    (by simpa [hermite] using (Nat.cast_ne_zero (R := K)).mpr n.succ_ne_zero)

/-- Consecutive probabilists' Hermite polynomials are coprime. -/
theorem isCoprime_hermite_succ {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    IsCoprime ((hermite K).p n) ((hermite K).p (n + 1)) :=
  (hermite K).isCoprime_succ isUnit_hermite_b n

end ThreeTermRecurrence

end Polynomial

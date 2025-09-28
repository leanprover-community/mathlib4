/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Damiano Testa, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Division
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Order.Interval.Finset.Nat

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/


noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

/-- `divX p` returns a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def divX (p : R[X]) : R[X] :=
  ⟨AddMonoidAlgebra.divOf p.toFinsupp 1⟩

@[simp]
theorem coeff_divX : (divX p).coeff n = p.coeff (n + 1) := by
  rw [add_comm]; cases p; rfl

theorem divX_mul_X_add (p : R[X]) : divX p * X + C (p.coeff 0) = p :=
  ext <| by rintro ⟨_ | _⟩ <;> simp [coeff_C, coeff_mul_X]

@[simp]
theorem X_mul_divX_add (p : R[X]) : X * divX p + C (p.coeff 0) = p :=
  ext <| by rintro ⟨_ | _⟩ <;> simp [coeff_C]

@[simp]
theorem divX_C (a : R) : divX (C a) = 0 :=
  ext fun n => by simp [coeff_divX]

theorem divX_eq_zero_iff : divX p = 0 ↔ p = C (p.coeff 0) :=
  ⟨fun h => by simpa [eq_comm, h] using divX_mul_X_add p, fun h => by rw [h, divX_C]⟩

theorem divX_add : divX (p + q) = divX p + divX q :=
  ext <| by simp

@[simp]
theorem divX_zero : divX (0 : R[X]) = 0 := leadingCoeff_eq_zero.mp rfl

@[simp]
theorem divX_one : divX (1 : R[X]) = 0 := by
  ext
  simpa only [coeff_divX, coeff_zero] using coeff_one

@[simp]
theorem divX_C_mul : divX (C a * p) = C a * divX p := by
  ext
  simp

theorem divX_X_pow : divX (X ^ n : R[X]) = if (n = 0) then 0 else X ^ (n - 1) := by
  cases n
  · simp
  · ext n
    simp [coeff_X_pow]

/-- `divX` as an additive homomorphism. -/
noncomputable
def divX_hom : R[X] →+ R[X] :=
  { toFun := divX
    map_zero' := divX_zero
    map_add' := fun _ _ => divX_add }

@[simp] theorem divX_hom_toFun : divX_hom p = divX p := rfl

theorem natDegree_divX_eq_natDegree_tsub_one : p.divX.natDegree = p.natDegree - 1 := by
  apply map_natDegree_eq_sub (φ := divX_hom)
  · intro f
    simpa [divX_hom, divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intro n c c0
    rw [← C_mul_X_pow_eq_monomial, divX_hom_toFun, divX_C_mul, divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0

theorem natDegree_divX_le : p.divX.natDegree ≤ p.natDegree :=
  natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)

theorem divX_C_mul_X_pow : divX (C a * X ^ n) = if n = 0 then 0 else C a * X ^ (n - 1) := by
  simp only [divX_C_mul, divX_X_pow, mul_ite, mul_zero]

theorem degree_divX_lt (hp0 : p ≠ 0) : (divX p).degree < p.degree := by
  haveI := Nontrivial.of_polynomial_ne hp0
  calc
    degree (divX p) < (divX p * X + C (p.coeff 0)).degree :=
      if h : degree p ≤ 0 then by
        have h' : C (p.coeff 0) ≠ 0 := by rwa [← eq_C_of_degree_le_zero h]
        rw [eq_C_of_degree_le_zero h, divX_C, degree_zero, zero_mul, zero_add]
        exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 <| by simpa using h'))
      else by
        have hXp0 : divX p ≠ 0 := by
          simpa [divX_eq_zero_iff, -not_le, degree_le_zero_iff] using h
        have : leadingCoeff (divX p) * leadingCoeff X ≠ 0 := by simpa
        have : degree (C (p.coeff 0)) < degree (divX p * X) :=
          calc
            degree (C (p.coeff 0)) ≤ 0 := degree_C_le
            _ < 1 := by decide
            _ = degree (X : R[X]) := degree_X.symm
            _ ≤ degree (divX p * X) := by
              rw [← zero_add (degree X), degree_mul' this]
              exact add_le_add
                (by rw [zero_le_degree_iff, Ne, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_elim]
noncomputable def recOnHorner {M : R[X] → Sort*} (p : R[X]) (M0 : M 0)
    (MC : ∀ p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a))
    (MX : ∀ p, p ≠ 0 → M p → M (p * X)) : M p :=
  letI := Classical.decEq R
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    rw [← divX_mul_X_add p] at *
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0, C_0, add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by p.degree

/-- A property holds for all polynomials of positive `degree` with coefficients in a semiring `R`
if it holds for
* `a * X`, with `a ∈ R`,
* `p * X`, with `p ∈ R[X]`,
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
with appropriate restrictions on each term.

See `natDegree_ne_zero_induction_on` for a similar statement involving no explicit multiplication.
-/
@[elab_as_elim]
theorem degree_pos_induction_on {P : R[X] → Prop} (p : R[X]) (h0 : 0 < degree p)
    (hC : ∀ {a}, a ≠ 0 → P (C a * X)) (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
    (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
  recOnHorner p (fun h => by rw [degree_zero] at h; exact absurd h (by decide))
    (fun p a heq0 _ ih h0 =>
      (have : 0 < degree p :=
        (lt_of_not_ge fun h =>
          not_lt_of_ge (degree_C_le (a := a)) <|
            by rwa [eq_C_of_degree_le_zero h, ← C_add,heq0,zero_add] at h0)
      hadd this (ih this)))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        exact hC fun h : coeff p 0 = 0 => by simp [h] at h0')
    h0

/-- A property holds for all polynomials of non-zero `natDegree` with coefficients in a
semiring `R` if it holds for
* `p + a`, with `a ∈ R`, `p ∈ R[X]`,
* `p + q`, with `p, q ∈ R[X]`,
* monomials with nonzero coefficient and non-zero exponent,
with appropriate restrictions on each term.
Note that multiplication is "hidden" in the assumption on monomials, so there is no explicit
multiplication in the statement.
See `degree_pos_induction_on` for a similar statement involving more explicit multiplications.
-/
@[elab_as_elim]
theorem natDegree_ne_zero_induction_on {M : R[X] → Prop} {f : R[X]} (f0 : f.natDegree ≠ 0)
    (h_C_add : ∀ {a p}, M p → M (C a + p)) (h_add : ∀ {p q}, M p → M q → M (p + q))
    (h_monomial : ∀ {n : ℕ} {a : R}, a ≠ 0 → n ≠ 0 → M (monomial n a)) : M f := by
  suffices f.natDegree = 0 ∨ M f from Or.recOn this (fun h => (f0 h).elim) id
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
  · rintro p q (hp | hp) (hq | hq)
    · refine Or.inl ?_
      rw [eq_C_of_natDegree_eq_zero hp, eq_C_of_natDegree_eq_zero hq, ← C_add, natDegree_C]
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hp]
      exact h_C_add hq
    · refine Or.inr ?_
      rw [eq_C_of_natDegree_eq_zero hq, add_comm]
      exact h_C_add hp
    · exact Or.inr (h_add hp hq)
  · intro n a _
    by_cases a0 : a = 0
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
    · refine Or.inr ?_
      rw [C_mul_X_pow_eq_monomial]
      exact h_monomial a0 n.succ_ne_zero

end Semiring

end Polynomial

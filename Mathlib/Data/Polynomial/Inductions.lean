/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Damiano Testa, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Division
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Induction

#align_import data.polynomial.inductions from "leanprover-community/mathlib"@"57e09a1296bfb4330ddf6624f1028ba186117d82"

/-!
# Induction on polynomials

This file contains lemmas dealing with different flavours of induction on polynomials.
-/


noncomputable section

open Classical BigOperators Polynomial

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
set_option linter.uppercaseLean3 false in
#align polynomial.div_X Polynomial.divX

@[simp]
theorem coeff_divX : (divX p).coeff n = p.coeff (n + 1) := by
  rw [add_comm]; cases p; rfl
  -- ⊢ coeff (divX p) n = coeff p (1 + n)
                 -- ⊢ coeff (divX { toFinsupp := toFinsupp✝ }) n = coeff { toFinsupp := toFinsupp✝ …
                          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.coeff_div_X Polynomial.coeff_divX

theorem divX_mul_X_add (p : R[X]) : divX p * X + C (p.coeff 0) = p :=
  ext <| by rintro ⟨_ | _⟩ <;> simp [coeff_C, Nat.succ_ne_zero, coeff_mul_X]
            -- ⊢ coeff (divX p * X + ↑C (coeff p 0)) Nat.zero = coeff p Nat.zero
                               -- 🎉 no goals
                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.div_X_mul_X_add Polynomial.divX_mul_X_add

@[simp]
theorem divX_C (a : R) : divX (C a) = 0 :=
  ext fun n => by simp [coeff_divX, coeff_C, Finsupp.single_eq_of_ne _]
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.div_X_C Polynomial.divX_C

theorem divX_eq_zero_iff : divX p = 0 ↔ p = C (p.coeff 0) :=
  ⟨fun h => by simpa [eq_comm, h] using divX_mul_X_add p, fun h => by rw [h, divX_C]⟩
               -- 🎉 no goals
                                                                      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.div_X_eq_zero_iff Polynomial.divX_eq_zero_iff

theorem divX_add : divX (p + q) = divX p + divX q :=
  ext <| by simp
            -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.div_X_add Polynomial.divX_add

theorem degree_divX_lt (hp0 : p ≠ 0) : (divX p).degree < p.degree := by
  haveI := Nontrivial.of_polynomial_ne hp0
  -- ⊢ degree (divX p) < degree p
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
                (by rw [zero_le_degree_iff, Ne.def, divX_eq_zero_iff]
                    exact fun h0 => h (h0.symm ▸ degree_C_le))
                    le_rfl
        rw [degree_add_eq_left_of_degree_lt this]; exact degree_lt_degree_mul_X hXp0
    _ = degree p := congr_arg _ (divX_mul_X_add _)
set_option linter.uppercaseLean3 false in
#align polynomial.degree_div_X_lt Polynomial.degree_divX_lt

/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_elim]
noncomputable def recOnHorner {M : R[X] → Sort*} (p : R[X]) (M0 : M 0)
    (MC : ∀ p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a))
    (MX : ∀ p, p ≠ 0 → M p → M (p * X)) : M p :=
  if hp : p = 0 then hp ▸ M0
  else by
    have wf : degree (divX p) < degree p := degree_divX_lt hp
    -- ⊢ M p
    rw [← divX_mul_X_add p] at *
    -- ⊢ M (divX p * X + ↑C (coeff p 0))
    exact
      if hcp0 : coeff p 0 = 0 then by
        rw [hcp0, C_0, add_zero]
        exact
          MX _ (fun h : divX p = 0 => by simp [h, hcp0] at hp) (recOnHorner (divX p) M0 MC MX)
      else
        MC _ _ (coeff_mul_X_zero _) hcp0
          (if hpX0 : divX p = 0 then show M (divX p * X) by rw [hpX0, zero_mul]; exact M0
          else MX (divX p) hpX0 (recOnHorner _ M0 MC MX))
termination_by _ => p.degree
#align polynomial.rec_on_horner Polynomial.recOnHorner

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
                             -- ⊢ P 0
                                                    -- 🎉 no goals
    (fun p a _ _ ih h0 =>
      have : 0 < degree p :=
        lt_of_not_ge fun h =>
          not_lt_of_ge degree_C_le <| by rwa [eq_C_of_degree_le_zero h, ← C_add] at h0
                                         -- 🎉 no goals
      hadd this (ih this))
    (fun p _ ih h0' =>
      if h0 : 0 < degree p then hX h0 (ih h0)
      else by
        rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at h0' ⊢
        -- ⊢ P (↑C (coeff p 0) * X)
        exact hC fun h : coeff p 0 = 0 => by simp [h, Nat.not_lt_zero] at h0')
        -- 🎉 no goals
    h0
#align polynomial.degree_pos_induction_on Polynomial.degree_pos_induction_on

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
  -- ⊢ natDegree f = 0 ∨ M f
  refine Polynomial.induction_on f ?_ ?_ ?_
  · exact fun a => Or.inl (natDegree_C _)
    -- 🎉 no goals
  · rintro p q (hp | hp) (hq | hq)
    · refine' Or.inl _
      -- ⊢ natDegree (p + q) = 0
      rw [eq_C_of_natDegree_eq_zero hp, eq_C_of_natDegree_eq_zero hq, ← C_add, natDegree_C]
      -- 🎉 no goals
    · refine' Or.inr _
      -- ⊢ M (p + q)
      rw [eq_C_of_natDegree_eq_zero hp]
      -- ⊢ M (↑C (coeff p 0) + q)
      exact h_C_add hq
      -- 🎉 no goals
    · refine' Or.inr _
      -- ⊢ M (p + q)
      rw [eq_C_of_natDegree_eq_zero hq, add_comm]
      -- ⊢ M (↑C (coeff q 0) + p)
      exact h_C_add hp
      -- 🎉 no goals
    · exact Or.inr (h_add hp hq)
      -- 🎉 no goals
  · intro n a _
    -- ⊢ natDegree (↑C a * X ^ (n + 1)) = 0 ∨ M (↑C a * X ^ (n + 1))
    by_cases a0 : a = 0
    -- ⊢ natDegree (↑C a * X ^ (n + 1)) = 0 ∨ M (↑C a * X ^ (n + 1))
    · exact Or.inl (by rw [a0, C_0, zero_mul, natDegree_zero])
      -- 🎉 no goals
    · refine' Or.inr _
      -- ⊢ M (↑C a * X ^ (n + 1))
      rw [C_mul_X_pow_eq_monomial]
      -- ⊢ M (↑(monomial (n + 1)) a)
      exact h_monomial a0 n.succ_ne_zero
      -- 🎉 no goals
#align polynomial.nat_degree_ne_zero_induction_on Polynomial.natDegree_ne_zero_induction_on

end Semiring

end Polynomial

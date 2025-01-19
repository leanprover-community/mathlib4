/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Basis.Basic

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

* Generalize linear independence of polynomial sequences to arbitrary sets of polynomials
  which are pairwise different degree.

-/

open Submodule (span)
open scoped Function

universe u

variable (R : Type u)

namespace Polynomial

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  elems' : ℕ → R[X]
  degree_eq' (i : ℕ) : (elems' i).degree = i

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems i`. -/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦  ℕ → R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

@[simp]
lemma degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

@[simp]
lemma natDegree_eq (i : ℕ) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some <| S.degree_eq i

/-- No polynomial in the sequence is zero. -/
lemma ne_zero (i : ℕ) : S i ≠ 0 := degree_ne_bot.mp (by simp [S.degree_eq i])

/-- No two elements in the sequence have the same degree. -/
lemma degree_ne_degree {i j : ℕ} (h : i ≠ j) : (S i).degree ≠ (S j).degree := by
  simp [S.degree_eq i, S.degree_eq j, h]

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- Polynomials in a polynomial sequence are linearly independent. -/
lemma linearIndependent [NoZeroDivisors R] :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := (fun i ↦ (g i • S i).degree))
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  · have hpairwise :
        {i | i ∈ s ∧ g i • S i ≠ 0}.Pairwise (Ne on (degree ∘ fun i ↦ g i • S i)) := by
      intro x ⟨xmem, hx⟩ y ⟨ymem, hy⟩ xney
      have hgxreg : IsSMulRegular R (g x) := by
        intro w v hwv
        have hgwv : g x • (w - v) = 0 := by rw [smul_sub, sub_eq_zero.mpr hwv]
        cases' mul_eq_zero.mp hgwv with hgx hwv'
        · exact (hx (by simp [hgx])).elim
        · exact sub_eq_zero.mp hwv'
      have hgyreg : IsSMulRegular R (g y) := by
        intro w v hwv
        have hgwv : g y • (w - v) = 0 := by rw [smul_sub, sub_eq_zero.mpr hwv]
        cases' mul_eq_zero.mp hgwv with hgy hwv'
        · exact (hy (by simp [hgy])).elim
        · exact sub_eq_zero.mp hwv'
      have hgx := degree_smul_of_smul_regular (S x) hgxreg
      have hgy := degree_smul_of_smul_regular (S y) hgyreg
      simpa [hgx, hgy] using S.degree_ne_degree xney

    obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S i).degree) = n := exists_eq'
    have hsum := degree_sum_eq_of_disjoint _ s hpairwise |>.trans hn
    have := hsum.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm
    exact degree_ne_bot.mp this eqzero |>.elim

section Nontrivial

variable [Nontrivial R]

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : ⊤ ≤ span R (Set.range S) := by
  intro P _
  induction' hp : P.natDegree using Nat.strong_induction_on with n ih generalizing P
  by_cases p_ne_zero : P ≠ 0
  · have is_unit := hCoeff n
    obtain ⟨u, hu⟩ := isUnit_iff_exists.mp is_unit

    have u_unit: IsUnit u := isUnit_iff_exists.mpr ⟨(S n).leadingCoeff, ⟨hu.2, hu.1⟩⟩

    let tail := P - (P.leadingCoeff • u • (S n))

    have tail_deg: tail.degree < n := by
      have u_cancel: (u • S n).leadingCoeff = 1 := by
        rw [leadingCoeff_smul_of_smul_regular]
        · exact hu.2
        · exact u_unit.isSMulRegular R

      have u_degree_same := degree_smul_of_leadingCoeff_rightRegular
        u_unit.ne_zero is_unit.isRegular.right

      have other := degree_smul_of_leadingCoeff_rightRegular
        (leadingCoeff_ne_zero.mpr p_ne_zero) (u_cancel ▸ isRegular_one.right)
      rw [u_degree_same, S.degree_eq n, ← hp, eq_comm, ← degree_eq_natDegree p_ne_zero, hp] at other

      have smul_nonzero: (P.leadingCoeff • u • S n) ≠ 0 := by
        by_cases n_eq_zero: n = 0
        · rw [n_eq_zero, ne_eq, eq_C_of_degree_eq_zero <| S.degree_eq 0,
              smul_C, smul_eq_mul, map_mul]
          rw [n_eq_zero, ← coeff_natDegree, natDegree_eq] at hu
          rw [← C_mul, hu.2, smul_C]
          simp [p_ne_zero]
        · have bar := (P.leadingCoeff • u • S n).ne_zero_of_degree_gt (n := 0)
          rw [← other] at bar
          have natdegree_gt_zero: 0 < P.natDegree := by omega
          have deg_gt_zero: 0 < P.degree := natDegree_pos_iff_degree_pos.mp natdegree_gt_zero
          exact bar deg_gt_zero

      have s_to_p_coeff: P.leadingCoeff = (P.leadingCoeff • (u • S n)).leadingCoeff := by
        rw [degree_eq_natDegree, degree_eq_natDegree smul_nonzero] at other
        rw [← coeff_natDegree] at u_cancel
        norm_cast at other
        nth_rw 2 [← coeff_natDegree]
        rw [← other, coeff_smul, hp]
        have s_deg := S.degree_eq n
        rw [degree_eq_natDegree (ne_zero S n)] at s_deg
        norm_cast at s_deg
        nth_rw 2 [ ← s_deg]
        rwa [coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, hu.2, mul_one]

      have foo := P.degree_sub_lt other p_ne_zero s_to_p_coeff
      rwa [degree_eq_natDegree p_ne_zero, hp] at foo

    have p_eq_sum: P = tail + P.leadingCoeff • u • S n := by
      exact Eq.symm (sub_add_cancel P (P.leadingCoeff • u • S n))

    have coeff_in_span: P.leadingCoeff • u • S n ∈ Submodule.span R (Set.range S) := by
      have n_in_range: S n ∈ Set.range S := by simp
      have in_span := Submodule.subset_span (R := R) (s := Set.range S) n_in_range
      have smul_span := Submodule.smul_mem
        (Submodule.span R (Set.range S)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span

    by_cases tail_eq_zero: tail = 0
    · simp [tail_eq_zero] at p_eq_sum
      rwa [← p_eq_sum] at coeff_in_span
    · have natdeg_lt_n := natDegree_lt_iff_degree_lt tail_eq_zero |>.mpr tail_deg
      simp only [Submodule.mem_top, forall_const] at ih
      have tail_in_span := ih tail.natDegree natdeg_lt_n rfl

      exact (Submodule.sub_mem_iff_left
        (Submodule.span R (Set.range S)) coeff_in_span).mp tail_in_span
  · rw [ne_eq, not_not] at p_ne_zero
    simp [p_ne_zero]

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis [NoZeroDivisors R] (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) :
    Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| S.span hCoeff

end Nontrivial

end Ring

end Sequence

end Polynomial

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.Regular
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent

/-!

# Polynomial sequences

## TODO

* Generalize linear independence of polynomial sequences to arbitrary sets of polynomials
  which are pairwise different degree.

-/

open Submodule (span)

universe u

variable (R : Type u) 

namespace Polynomial

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  elems : ℕ → R[X]
  degree_eq (i : ℕ) : (elems i).degree = i

/-- No polynomial in the sequence is zero. -/
lemma Sequence.ne_zero {R} (i : ℕ) [Semiring R] (S : Sequence R) : S.elems i ≠ 0 :=
  degree_ne_bot.mp (by simp [S.degree_eq i])

namespace Sequence

variable {R}

section Semiring

variable [Semiring R] (S : Sequence R) 

/-- No two elements in the sequence have the same degree. -/
lemma degree_ne {i j : ℕ} (h : i ≠ j) : (S.elems i).degree ≠ (S.elems j).degree := by
  simp [S.degree_eq i, S.degree_eq j, h]

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

open scoped Function in
/-- Polynomials in a polynomial sequence are linearly independent. -/
lemma linearIndependent [NoZeroDivisors R] :
    LinearIndependent R S.elems := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S.elems i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := (fun i ↦ (g i • S.elems i).degree))
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  · have hpairwise :
        {i | i ∈ s ∧ g i • S.elems i ≠ 0}.Pairwise (Ne on (degree ∘ fun i ↦ g i • S.elems i)) := by
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
      have hgx := degree_smul_of_smul_regular (S.elems x) hgxreg
      have hgy := degree_smul_of_smul_regular (S.elems y) hgyreg
      simpa [hgx, hgy] using S.degree_ne xney

    obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S.elems i).degree) = n := exists_eq'
    have hsum := degree_sum_eq_of_disjoint _ s hpairwise |>.trans hn
    have := hsum.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm
    exact degree_ne_bot.mp this eqzero |>.elim

/-- A polynomial sequence over `R` spans `R[X]`. -/
lemma span (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) : ⊤ ≤ span R (Set.range S.elems) := by
  sorry

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis [NoZeroDivisors R] (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) :
    Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| S.span hCoeff

end Ring

end Sequence

end Polynomial

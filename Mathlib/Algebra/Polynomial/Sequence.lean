import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.Regular
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent

/-!

# Polynomial sequences

-/

open Submodule (span)

universe u

variable (R : Type u) 

namespace Polynomial

example [Ring R] (p q : R[X]) (h : p.degree < q.degree) (hp : p ≠ 0) :
    LinearIndependent R ![p, q] := by
  refine LinearIndependent.pair_iff.mpr fun s t hs ↦ ?_
  conv_lhs at hs => equals s • p - -t • q => rw [neg_smul, ← (sub_neg_eq_add (s • p) (t • q))]
  have := degree_sub_eq_right_of_degree_lt h
  by_contra h'
  have : s ≠ 0 ∨ t ≠ 0 := by simp [←not_and_or, h']
  rcases this with hS | hT
  · have : (s • p).degree = p.degree := by
      refine degree_smul_of_smul_regular p ?_
      sorry
    sorry
  · sorry

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

variable [Ring R] (S : Sequence R) -- #20480

-- TODO: Generalize to any set of polynomials with different degrees
open scoped Function in
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

lemma span (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) : ⊤ ≤ span R (Set.range S.elems) := by
  sorry

noncomputable def basis (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| S.span hCoeff

end Ring

end Sequence

end Polynomial

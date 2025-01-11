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

open scoped Function in
lemma Sequence.degree_disjoint [Semiring R] (S : Sequence R) :
    (Set.range S.elems).Pairwise (Ne on degree) := by
  sorry

lemma Sequence.ne_zero {R} (i : ℕ) [Semiring R] (S : Sequence R) : S.elems i ≠ 0 := sorry

namespace Sequence

variable {R} [Ring R] (S : Sequence R) -- #20480

lemma linearIndependent_aux (n : ℕ) (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) :
    LinearIndependent R fun ν : Fin n => S.elems ν := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n hn => sorry

-- TODO: Generalize to any set of polynomials with different degrees
open scoped Function in
lemma linearIndependent [NoZeroSMulDivisors R R[X]] :
    LinearIndependent R S.elems := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  -- have giregular := isRegular_of_ne_zero' _
  -- have := degree_smul_of_smul_regular (S.elems i) giregular.left.isSMulRegular
  have hpairwise :
      {i | i ∈ s ∧ g i • S.elems i ≠ 0}.Pairwise (Ne on (degree ∘ fun i ↦ g i • S.elems i)) :=
    sorry 
  by_cases hsupzero : s.sup (fun i ↦ (g i • S.elems i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := (fun i ↦ (g i • S.elems i).degree))
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  · obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S.elems i).degree) = n := exists_eq'
    have hsum := degree_sum_eq_of_disjoint _ s hpairwise |>.trans hn
    have := degree_ne_bot.mp <| hsum.trans_ne <|.symm (ne_of_ne_of_eq (hsupzero ·.symm) hn)
    contradiction

lemma span (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) : ⊤ ≤ span R (Set.range S.elems) := by
  sorry

noncomputable def basis (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| S.span hCoeff

end Sequence

end Polynomial

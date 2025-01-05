import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent

/-!

# Polynomial sequences

-/

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

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence' {ι : Type*} [CoeOTC ι (WithBot ℕ)] [Semiring R] where
  elems : ι → R[X]
  degree_eq (i : ι) : (elems i).degree = ↑i

noncomputable def S [Nontrivial R] [Semiring R] : Sequence' R ℕ where
  elems (i : ℕ) := X ^ i
  degree_eq (i : ℕ) := by rw [degree_X_pow]; rfl

noncomputable def S_fin [Nontrivial R] [Semiring R] : Sequence' R (Fin 6) where
  elems (i : Fin 6) := X ^ ↑i
  degree_eq (i : Fin 6) := by rw [degree_X_pow]; rfl

namespace Sequence

variable {R} [Ring R] (S : Sequence R) -- #20480

lemma linearIndependent_aux (n : ℕ) (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) :
    LinearIndependent R fun ν : Fin n => S.elems ν := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n hn => sorry

theorem linearIndependent (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) :
    LinearIndependent R S.elems := by
  apply?

lemma span (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) :
    ⊤ ≤ Submodule.span R (Set.range S.elems) := by
  sorry

noncomputable def basis (hCoeff : ∀ i, (S.elems i).leadingCoeff = 1) : Basis ℕ R R[X] :=
  Basis.mk (S.linearIndependent hCoeff) (S.span hCoeff)

end Sequence

end Polynomial

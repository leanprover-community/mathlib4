/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent

/-!

# Bases of polynomial rings

-/

universe u

variable (R : Type u)

namespace Polynomial

section monomials

variable [Semiring R]

/-- The monomials form a basis on `R[X]`. To get the rank of a polynomial ring,
use this and `Basis.mk_eq_rank`. -/
def basisMonomials : Basis ℕ R R[X] :=
  Basis.ofRepr (toFinsuppIsoLinear R)

@[simp]
theorem coe_basisMonomials : (basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 :=
  funext fun _ => ofFinsupp_single _ _

end monomials

section degreeSequence

variable [CommRing R] [IsDomain R] {Q : ℕ → R[X]}

example (p q : R[X]) (h : p.degree < q.degree) (hp : p ≠ 0) : LinearIndependent R ![p, q] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t hs
  conv at hs =>
    lhs
    equals s • p - -t • q =>
      rw [neg_smul]
      exact (sub_neg_eq_add (s • p) (t • q)).symm
  have := degree_sub_eq_right_of_degree_lt h
  by_contra h'
  have : s ≠ 0 ∨ t ≠ 0 := by simp [←not_and_or, h']
  rcases this with hS | hT
  · have : (s • p).degree = p.degree := by
      refine degree_smul_of_smul_regular p ?_
      apply IsSMulRegular.of_smul
    sorry
  · sorry

theorem degreeSequence_linearIndependent_aux (n k : ℕ) (h : k ≤ n + 1) (hQ : ∀ i, (Q i).degree = i) :
    LinearIndependent R fun ν : Fin k => Q ν := by
  induction' k with k ih
  · apply linearIndependent_empty_type
  · have := hQ (n + 1)
    have := LinearIndependent

theorem degreeSequence_linearIndependent (n : ℕ) (hQ : ∀ i, (Q i).degree = i) :
    LinearIndependent R fun ν : Fin (n + 1) ↦ Q n := by
  linearIndependent_aux n (n + 1) le_rfl

def basisDegreeSequence {Q : ℕ → R[X]} (hQ : ∀ i, (Q i).degree = i) : Basis ℕ R R[X] :=
  Basis.mk degreeSequence_linearIndependent sorry

end degreeSequence

end Polynomial

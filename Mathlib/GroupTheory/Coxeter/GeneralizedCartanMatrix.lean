/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/- # Generalized Cartan matrices

Let `M` be a Coxeter matrix indexed by a type `B`. (See `Mathlib/GroupTheory/Coxeter/Matrix.lean`
and `Mathlib/GroupTheory/Coxeter/Basic.lean`.)

Traditionally, a geometric representation of a Coxeter group with Coxeter matrix $M$ is defined by
starting with a matrix $(k_{i, i})_{i, i' \in B}$ satisfying the following conditions for all
$i, i'$:
1. $k_{i, i} = 2$.
2. $k_{i, i'} = 0$ if and only if $M_{i, i'} = 2$.
3. $k_{i, i'} \leq 0$ for $i \neq i'$.
4. $k_{i, i'} k_{i', i} = 4 \cos^2 (\pi / M_{i, i'})$ if $M_{i, i'} \neq 0$.
5. $k_{i, i'} k_{i', i} \geq 4$ if $M_{i, i'} = 0$.
(For example, see
https://www.math.cuhk.edu.hk/course_builder/2223/math6032/lecture-notes-coxeter.pdf, page 9.) The
matrix $(k_{i, i})_{i, i' \in B}$ can then be used to define a representation of $W$ over the real
numbers.

Fix a commutative ordered ring $R$, not necessarily the ring of real numbers. In this file, we
define a *generalized Cartan matrix for $M$* (`CoxeterMatrix.GeneralizedCartanMatrix`) to be a
matrix with entries in $R$ that satisfies a suitable generalization of conditions 1–5 above.

TODO: Add "main definitions" docstring
-/

open Polynomial.Chebyshev Real

variable {B : Type*}

namespace CoxeterMatrix

/-- Fix a Coxeter matrix (`CoxeterMatrix`) $M$ whose rows and columns are indexed by a type $B$.
Let $(k_{i, i'})_{i, i' \in B}$ be a matrix whose entries lie in a commutative ordered ring $R$.
We say that $k$ is a *generalized Cartan matrix* for $M$ if for all $i, i'$, we have
1. $k_{i, i} = 2$.
2. $k_{i, i'} = 0$ if and only if $M_{i, i'} = 2$.
3. If $m = M_{i, i'}$ is even, then $S_{m/2 - 1}(k_{i, i'} k_{i', i} - 2) = 0$, where $S$ refers to
  a Chebyshev $S$-polynomial (`Polynomial.Chebyshev.S`).
4. If $m = M_{i, i'}$ is odd, then
  $S_{(m-1)/2}(k_{i, i'} k_{i', i} - 2) + S_{(m-3)/2}(k_{i, i'} k_{i', i} - 2) = 0$.
5. For $0 \leq j \leq M_{i, i'} / 2 - 1$, we have $S_{j}(k_{i, i'} k_{i', i} - 2) \geq 0$.
6. If $M_{i, i'} = 0$, then $S_{j}(k_{i, i'} k_{i', i} - 2) \geq 0$ for all $j \geq 0$.
Generalized Cartan matrices can be used to define reflection representations of the Coxeter group
corresponding to the Coxeter matrix $M$. -/
@[mk_iff]
structure IsGeneralizedCartan {R : Type*} [OrderedCommRing R] (M : CoxeterMatrix B)
    (k : Matrix B B R) : Prop where
  diagonal i : k i i = 2
  eq_zero_iff i i' : k i i' = 0 ↔ M i i' = 2
  s_eval_eq_zero_of_even i i' (j : ℤ) (_ : M i i' = 2 * j) :
    Polynomial.eval (k i i' * k i' i - 2) (S R (j - 1)) = 0
  s_eval_eq_zero_of_odd i i' (j : ℤ) (_ : M i i' = 2 * j + 1) :
    Polynomial.eval (k i i' * k i' i - 2) (S R (j - 1)) +
      Polynomial.eval (k i i' * k i' i - 2) (S R j) = 0
  s_eval_nonneg i i' (j : ℕ) (_ : 2 * j + 2 ≤ M i i') :
    Polynomial.eval (k i i' * k i' i - 2) (S R j) ≥ 0
  s_eval_nonneg' i i' (j : ℕ) (_ : M i i' = 0) :
    Polynomial.eval (k i i' * k i' i - 2) (S R j) ≥ 0

/-- Fix a Coxeter matrix (`CoxeterMatrix`) $M$ whose rows and columns are indexed by a type $B$.
Let $(k_{i, i'})_{i, i' \in B}$ be a matrix with real entries. We say that $k$ is a
*generalized Cartan matrix* for $M$ if for all $i, i'$, we have
1. $k_{i, i} = 2$.
2. $k_{i, i'} = 0$ if and only if $M_{i, i'} = 2$.
3. $k_{i, i'} \leq 0$ for $i \neq i'$.
4. $k_{i, i'} k_{i', i} = 4 \cos^2 (\pi / M_{i, i'})$ if $M_{i, i'} \neq 0$.
5. $k_{i, i'} k_{i', i} \geq 4$ if $M_{i, i'} = 0$.
This is the classical definition of a generalized Cartan matrix. It is equivalent to the definition
given in `CoxeterMatrix.IsGeneralizedCartan`, but it only makes sense for matrices with real
entries. -/
@[mk_iff]
structure IsRealGeneralizedCartan (M : CoxeterMatrix B) (k : Matrix B B ℝ) :
    Prop where
  diagonal i : k i i = 2
  eq_zero_iff i i' : k i i' = 0 ↔ M i i' = 2
  leq_zero i i' (_ : i ≠ i) : k i i' ≤ 0
  mul_eq_four_mul_cos_sq i i' (_ : M i i' ≠ 0) : k i i' * k i' i = 4 * cos (π / M i i') ^ 2
  mul_ge_four i i' (_ : M i i' = 0) : 4 ≤ k i i' * k i' i


/-- Fix a Coxeter matrix (`CoxeterMatrix`) $M$ whose rows and columns are indexed by a type $B$.
Let $(k_{i, i'})_{i, i' \in B}$ be a matrix with integer entries. We say that $k$ is a
*generalized Cartan matrix* for $M$ if for all $i, i'$, the ordered triple
`(M i i', k i i', k i' i)` is one of `(1, 2, 2)`, `(2, 0, 0)`, `(3, 1, 1)`, `(4, 1, 2)`,
`(4, 2, 1)`, `(6, 1, 3)`, `(6, 3, 1)`, or `(0, a, b)` with `a * b ≥ 4`.
This is equivalent to the definition given in `CoxeterMatrix.IsGeneralizedCartan`, but it only makes
sense for matrices with integer entries. -/
@[mk_iff]
structure IsIntegerGeneralizedCartan (M : CoxeterMatrix B) (k : Matrix B B ℤ) :
    Prop where
  mul_eq_four_mul_cos_sq i i' (_ : M i i' ≠ 0) :
    M i i' = 1 ∧ k i i' = 2 ∧ k i' i = 2 ∨
    M i i' = 2 ∧ k i i' = 0 ∧ k i' i = 0 ∨
    M i i' = 3 ∧ k i i' = 1 ∧ k i' i = 1 ∨
    M i i' = 4 ∧ k i i' = 1 ∧ k i' i = 2 ∨
    M i i' = 4 ∧ k i i' = 2 ∧ k i' i = 1 ∨
    M i i' = 6 ∧ k i i' = 1 ∧ k i' i = 3 ∨
    M i i' = 6 ∧ k i i' = 3 ∧ k i' i = 1
  mul_ge_four i i' (_ : M i i' = 0) : 4 ≤ k i i' * k i' i

/-- It is decidable whether a finite matrix with integer entries is a generalized Cartan matrix for
$M$. -/
instance [Fintype B] (M : CoxeterMatrix B) (k : Matrix B B ℤ) :
    Decidable (M.IsIntegerGeneralizedCartan k) :=
  decidable_of_iff' _ (isIntegerGeneralizedCartan_iff M k)

theorem isGeneralizedCartan_iff_isRealGeneralizedCartan (M : CoxeterMatrix B) (k : Matrix B B ℝ) :
    M.IsGeneralizedCartan k ↔ M.IsRealGeneralizedCartan k := sorry

theorem isGeneralizedCartan_iff_isIntegerGeneralizedCartan (M : CoxeterMatrix B)
    (k : Matrix B B ℤ) : M.IsGeneralizedCartan k ↔ M.IsIntegerGeneralizedCartan k := sorry

-- TODO: Map a generalized Cartan matrix via a monotone ring homomorphism or algebraMap

/-! ### Bundled generalized Cartan matrices -/

/-- The type of all generalized Cartan matrices for $M$ with entries in a commutative ordered ring
$R$. This is a bundled version of `CoxeterMatrix.IsGeneralizedCartan`. -/
structure GeneralizedCartanMatrix (M : CoxeterMatrix B) (R : Type*)
    [OrderedCommRing R] where
  val : Matrix B B R
  isGeneralizedCartan : M.IsGeneralizedCartan val

end CoxeterMatrix

namespace CoxeterMatrix.GeneralizedCartanMatrix

variable {R : Type*} [OrderedCommRing R] {M : CoxeterMatrix B} (k : M.GeneralizedCartanMatrix R)

/-- A generalized Cartan matrix can be coerced to a matrix. -/
instance : CoeFun (CoxeterMatrix.GeneralizedCartanMatrix M R) fun _ ↦ (Matrix B B R) := ⟨val⟩

@[simp]
lemma diagonal (i) : k i i = 2 := k.isGeneralizedCartan.diagonal i

lemma eq_zero_iff (i i') : k i i' = 0 ↔ M i i' = 2 := k.isGeneralizedCartan.eq_zero_iff i i'

lemma coxeterMatrix_eq_two (i i') : k i i' = 0 → M i i' = 2 := (k.eq_zero_iff i i').mp

lemma eq_zero (i i') : M i i' = 2 → k i i' = 0 := (k.eq_zero_iff i i').mpr

-- Continue this and add lemmas for the real and integer things

end CoxeterMatrix.GeneralizedCartanMatrix

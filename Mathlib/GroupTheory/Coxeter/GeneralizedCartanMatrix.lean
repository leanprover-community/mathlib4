/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.RingTheory.Polynomial.Chebyshev

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
define a *generalized Cartan matrix for $M$* to be a matrix with entries in $R$ that satisfies a
suitable generalization of conditions 1–5 above. Namely, for all $i, i'$, we have
1. $k_{i, i} = 2$.
2. $k_{i, i'} = 0$ if and only if $M_{i, i'} = 2$.
3. If $m = M_{i, i'}$ is even, then $S_{m/2 - 1}(k_{i, i'} k_{i', i} - 2) = 0$, where $S$ refers to
  a Chebyshev $S$-polynomial (`Polynomial.Chebyshev.S`).
4. If $m = M_{i, i'}$ is odd, then
  $S_{(m-1)/2}(k_{i, i'} k_{i', i} - 2) + S_{(m-3)/2}(k_{i, i'} k_{i', i} - 2) = 0$.
5. For $0 \leq j \leq M_{i, i'} / 2 - 1$, we have $S_{j}(k_{i, i'} k_{i', i} - 2) \geq 0$.
6. If $M_{i, i'} = 0$, then $S_{j}(k_{i, i'} k_{i', i} - 2) \geq 0$ for all $j \geq 0$.
If $R = \mathbb{R}$, then this is equivalent to conditions 1–5 above.

-/

open Polynomial.Chebyshev

variable {B R R' : Type*} [OrderedCommRing R] [OrderedCommRing R']

structure Matrix.IsGeneralizedCartanFor (k : Matrix B B R) (M : CoxeterMatrix B) : Prop where
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

namespace Matrix.IsGeneralizedCartanFor

end Matrix.IsGeneralizedCartanFor

/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Cartan matrices and their generalizations

The material in this file will be used to construct reflection representations of Coxeter groups.

Let $M$ be a Coxeter matrix (`CoxeterMatrix`) and let $W$ be a corresponding Coxeter group
(`CoxeterSystem`). Recall that each entry of $M$ is a positive integer or $0$, with $0$ indicating
no relation between the corresponding simple reflections in $W$. Let $k$ be a matrix with real
entries with the same dimensions as $M$. Consider the following properties that the matrix $k$ could
satisfy.

1. For all $i$, we have $k_{i, i} = 2$.
2. For all $i, i'$ with $2 \leq M_{i, i'}$, the number $k_{i, i'}k_{i', i}$ is of the form
  $4 \cos^2(\pi \ell / M_{i, i'})$, where $\ell$ is an integer with $0 < \ell \leq M_{i, i'} / 2$.
3. For all $i, i'$, we have $k_{i, i'} = 0$ if and only if $k_{i', i} = 0$.
4. (strengthening of 2) For all $i, i'$ with $M_{i, i'} \neq 0$, we have
  $k_{i,i'}k_{i', i} = 4 \cos^2(\pi / M_{i, i'})$.
5. For all $i, i'$ with $M_{i, i'} = 0$, we have $k_{i,i'}k_{i', i} \geq 4$.
6. For all $i \neq i'$, we have $k_{i, i'} \leq 0$.
7. The entries of $k$ are all integers.
8. The matrix $k$ is symmetrizable; that is, it can be written as $DS$, where $D$ is a diagonal
  matrix with positive entries and $S$ is a symmetric matrix.
9. (strengthening of 8) The matrix $k$ can be written as $DS$, where $D$ is a diagonal matrix with
  positive entries and $S$ is a symmetric and positive definite matrix.

It is not difficult to show that a matrix $k$ is a Cartan matrix
(`Mathlib.Algebra.Lie.CartanMatrix`) if and only if there exists a Coxeter matrix $M$ for which $k$
satisfies all nine of these properties. If so, the Coxeter matrix $M$ is unique. Any Cartan
matrix can be used to construct a reflection representation of the Coxeter group $W$, which can be
described as follows.
* The representation is on a real vector space $V$, called the *root space*.
* There are elements $\alpha_i \in V$, called the *simple roots*. The simple roots form a basis of
  $V$.
* There are elements $\alpha^\vee_i \in V^*$, called the *simple coroots*. They are given by
  $k_{i, i'} = \alpha^\vee_i(\alpha_{i'})$ for all $i, i'$.
* The simple reflection $s_i$ acts by a reflection (`Module.reflection`):
  $s_i v = v - \alpha^\vee_i (v)\alpha_i$.

However, we do not actually need the matrix $k$ to satisfy all 10 of the above properties in order
to get a reflection representation of $W$ as above. Namely:

* Only properties 1, 2, and 3 are necessary for the matrix $k$ to actually yield a reflection
  representation of $W$.
* If $k$ satisfies properties 1, 2, 3, 4, 5, 6, then this reflection representation is a
  *geometric representation*. That is, every element $w \alpha_i \in V$ is either a nonpositive
  linear combination of the simple roots or a nonnegative linear combination of the simple roots,
  according to whether $s_i$ is a right descent of $w$ or not. (This implies that the representation
  is faithful.)
* If $k$ satisfies properties 1, 2, 3, and 7, then this reflection representation is
  *crystallographic*. That is, it fixes the root lattice $\bigoplus_i\mathbb{Z} \alpha_i$.
* If $k$ satisfies properties 1, 2, 3, and 8, then this reflection representation comes with its own
  invariant bilinear form. This bilinear form, considered as a linear map $V \to V^*$, sends each
  simple root $\alpha_i$ to a positive multiple of the corresponding simple coroot $\alpha^\vee_i$.
* If $k$ satisfies properties 1, 2, 3, 8, and 9, then the aforementioned bilinear form is an inner
  product on $V$. (If $k$ satisfies properties 1, 2, 3, 4, 5, 6, 8, and 9, then this implies that
  the group $W$ is finite.)

## Main definitions and results

For this reason, we make the following definitions:

* We say that a matrix $k$ is *Cartan reflective* (`CoxeterMatrix.IsCartanReflective`) if it
  satisfies properties 1, 2, and 3 above.
* TODO: We say that a matrix $k$ is *Cartan geometric* if it satisfies properties 1, 2, 3, 4, 5, and
  6 above. (These conditions have appeared together in Equation 4.1–4.3 of [bjorner2005] and in
  Section 4 of https://www.math.cuhk.edu.hk/course_builder/2223/math6032/lecture-notes-coxeter.pdf.)
* TODO: As is standard in the literature, we say that a matrix $k$ with integer entries is simply
  a *Cartan matrix* if its diagonal entries are $2$, its off-diagonal entries are nonpositive, and
  it can be written as $DS$, where $D$ is a diagonal matrix with positive entries and $S$ is a
  symmetric and positive definite matrix. We prove that every Cartan matrix has a unique
  corresponding Coxeter matrix for which it satisfies all nine properties above.

These definitions are slightly modified to make sense over any ordered ring; see the implementation
details below.

## Implementation details

Using Chebyshev $S$-polynomials (`Polynomial.Chebyshev.S`), we can rewrite properties 1–9 so that
they do not involve the cosine function. That way, they make sense for matrices with entries in any
ordered ring. That is the approach we take here. Hence, there is no need to formalize property 7,
because we can simply take the ring to be $\mathbb{Z}$. We prove that if the ring is $\mathbb{R}$,
then the definitions using Chebyshev polynomials are equivalent to the definitions using the cosine
function.

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

open Polynomial.Chebyshev Real

variable {B : Type*} {R : Type*}

namespace CoxeterMatrix

/-! ### Cartan reflective matrices -/

/-- Fix a Coxeter matrix (`CoxeterMatrix`) $M$ whose rows and columns are indexed by a type $B$.
Let $(k_{i, i'})_{i, i' \in B}$ be a matrix with entries in a commutative ring $R$.
We say that $k$ is a *Cartan reflective matrix* for $M$ if:
* For all $i$, we have $k_{i, i} = 2$.
* For all $i, i'$, if $m = M_{i, i'}$ is even, then either $k_{i, i'} = k_{i', i} = 0$ or
  $S_{m/2 - 1}(k_{i, i'} k_{i', i} - 2) = 0$, where $S$ refers to a Chebyshev $S$-polynomial
  (`Polynomial.Chebyshev.S`).
* For all $i, i'$, if $m = M_{i, i'}$ is odd, then either $i = i'$ or
  $S_{(m-1)/2}(k_{i, i'} k_{i', i} - 2) + S_{(m-3)/2}(k_{i, i'} k_{i', i} - 2) = 0$.
Cartan reflective matrices can be used to define reflection representations of the Coxeter group
corresponding to the Coxeter matrix $M$. -/
@[mk_iff]
structure IsCartanReflective [CommRing R] (M : CoxeterMatrix B) (k : Matrix B B R) : Prop where
  diagonal i : k i i = 2
  s_eval_eq_zero_of_even i i' j :
    M i i' = 2 * j → k i i' = 0 ∧ k i' i = 0 ∨ (S R (j - 1)).eval (k i i' * k i' i - 2) = 0
  s_eval_eq_zero_of_odd i i' j :
    M i i' = 2 * j + 1 → i = i' ∨ (S R (j - 1)).eval (k i i' * k i' i - 2) +
      (S R j).eval (k i i' * k i' i - 2) = 0

/-- Fix a Coxeter matrix (`CoxeterMatrix`) $M$ whose rows and columns are indexed by a type $B$.
Let $(k_{i, i'})_{i, i' \in B}$ be a matrix with real entries.
We say that $k$ is a *Cartan reflective matrix* for $M$ if it satisfies properties 1, 2, and 3
from the top of this page. That is:
1. For all $i$, we have $k_{i, i} = 2$.
2. For all $i, i'$ with $2 \leq M_{i, i'}$, the number $k_{i, i'}k_{i', i}$ is of the form
  $4 \cos^2(\pi \ell / M_{i, i'})$, where $\ell$ is an integer with $0 < \ell \leq M_{i, i'} / 2$.
3. For all $i, i'$, we have $k_{i, i'} = 0$ if and only if $k_{i', i} = 0$.
This is equivalent to the previous definition of a Cartan reflective matrix (`IsCartanReflective`),
but specialized to matrices with real entries. -/
@[mk_iff]
structure IsRealCartanReflective (M : CoxeterMatrix B) (k : Matrix B B ℝ) : Prop where
  diagonal i : k i i = 2
  mul_eq_four_mul_cos_sq i i' : 2 ≤ M i i' → ∃ (ℓ : ℕ),
    0 < ℓ ∧ 2 * ℓ ≤ M i i' ∧ k i i' * k i' i = 4 * cos (ℓ * π / M i i') ^ 2
  eq_zero_iff i i' : k i i' = 0 ↔ k i' i = 0

theorem isRealCartanReflective_of_isCartanReflective (M : CoxeterMatrix B) (k : Matrix B B ℝ)
    (h : M.IsCartanReflective k) : M.IsRealCartanReflective k where
  diagonal i := h.diagonal i
  mul_eq_four_mul_cos_sq i i' (hii' : 2 ≤ M i i') := by
    have Mii'_ne_zero : M i i' ≠ 0 := by omega
    -- Rewrite `k i i' * k i' i - 2` as `2 * Complex.cos θ` for some `θ : ℂ`.
    obtain ⟨θ, hθ⟩ := Complex.cos_surjective (((k i i' * k i' i - 2 : ℝ) : ℂ) / 2)
    have eq_two_mul_cos_theta : ((k i i' * k i' i - 2 : ℝ) : ℂ) = 2 * Complex.cos θ := by
      rw [hθ]
      ring
    /- It suffices to show that `cos θ ≠ 1` and that there exists an integer `ℓ` such that
    `θ = ℓ * (2 * π) / M i i'`. -/
    have suffices_exists_ℓ : Complex.cos θ ≠ 1 → (∃ (ℓ : ℤ), θ = ℓ * (2 * π) / M i i')
      → ∃ ℓ, 0 < ℓ ∧ 2 * ℓ ≤ M i i' ∧ k i i' * k i' i = 4 * cos (ℓ * π / M i i') ^ 2 := by
      intro cos_θ_ne_one ⟨ℓ, hℓ⟩
      set ℓ' := Int.natAbs (Int.bmod ℓ (M i i')) with hℓ'
      set θ' := ℓ' * (2 * π) / (M i i') with hθ'
      have cos_θ'_eq_cos_θ : Real.cos θ' = Complex.cos θ := by
        unfold θ' ℓ'
        rw [hℓ, Int.cast_natAbs, Int.cast_abs, mul_div_assoc,
          ← abs_eq_self.mpr (show (2 * π) / M i i' ≥ 0 by positivity), ← abs_mul, cos_abs,
          Int.bmod_def, Int.emod_def]
        norm_cast
        split
        · push_cast
          rw [sub_mul, mul_comm (M i i' : ℝ), mul_assoc, mul_div_cancel₀ _ (mod_cast Mii'_ne_zero),
            cos_sub_int_mul_two_pi, ← mul_div_assoc]
        · push_cast
          rw [sub_mul, sub_mul, mul_comm (M i i' : ℝ), mul_assoc,
            mul_div_cancel₀ _ (mod_cast Mii'_ne_zero), cos_sub_two_pi, cos_sub_int_mul_two_pi,
            ← mul_div_assoc]
      use ℓ'
      refine ⟨?_, ?_, ?_⟩
      · show 0 < ℓ'
        have cos_θ'_ne_one : cos θ' ≠ 1 := by
          intro h
          rw [h, Complex.ofReal_one] at cos_θ'_eq_cos_θ
          tauto
        have ℓ'_ne_zero : ℓ' ≠ 0 := by
          intro h
          rw [h] at hθ'
          simp [hθ'] at cos_θ'_ne_one
        exact Nat.zero_lt_of_ne_zero ℓ'_ne_zero
      · show 2 * ℓ' ≤ M i i'
        unfold ℓ'
        have := Int.bmod_le (x := ℓ) (Nat.zero_lt_of_ne_zero Mii'_ne_zero)
        have := Int.le_bmod (x := ℓ) (Nat.zero_lt_of_ne_zero Mii'_ne_zero)
        omega
      · show k i i' * k i' i = 4 * cos (ℓ' * π / M i i') ^ 2
        apply Complex.ofReal_injective
        rw [Real.cos_sq, mul_div, mul_left_comm, ← hθ']
        push_cast at eq_two_mul_cos_theta cos_θ'_eq_cos_θ ⊢
        rw [cos_θ'_eq_cos_θ]
        linear_combination eq_two_mul_cos_theta
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (M.M i i')
    · obtain ⟨hkii', hki'i⟩ | S_eval_eq_zero := h.s_eval_eq_zero_of_even i i' j hj
      · use j, by omega, by omega
        simp [hkii', hki'i, hj, mul_comm _ π,
          mul_div_mul_right π 2 (show (j : ℝ) ≠ 0 by norm_cast; omega)]
      · have S_eval_eq_zero_complex : (S ℂ (j - 1)).eval (2 * Complex.cos θ) = 0 :=
          eq_two_mul_cos_theta ▸ mod_cast S_eval_eq_zero
        apply suffices_exists_ℓ
        · show Complex.cos θ ≠ 1
          intro cos_θ_eq_one
          rw [cos_θ_eq_one] at S_eval_eq_zero_complex
          simp at S_eval_eq_zero_complex
          omega
        · have eval_s_mul_sin_eq_zero := congrArg (· * Complex.sin θ) S_eval_eq_zero_complex
          simp only [S_two_mul_complex_cos, zero_mul] at eval_s_mul_sin_eq_zero
          push_cast at eval_s_mul_sin_eq_zero
          simp only [sub_add_cancel] at eval_s_mul_sin_eq_zero
          -- If `M i i' = 2 * j` is even, then we conclude that `sin (j * θ) = 0`.
          guard_hyp eval_s_mul_sin_eq_zero : Complex.sin (j * θ) = 0
          -- It follows that `j * θ` is an integer multiple of `π`.
          obtain ⟨ℓ, hℓ⟩ := Complex.sin_eq_zero_iff.mp eval_s_mul_sin_eq_zero
          use ℓ * j
          rw [hj]
          push_cast
          linear_combination (norm := field_simp) (1 / j) * hℓ
          sorry
    · sorry
  eq_zero_iff i i' := by
    suffices ∀ i i', k i i' = 0 → k i' i = 0 from ⟨this i i', this i' i⟩
    intro i i' hii'
    sorry

end CoxeterMatrix

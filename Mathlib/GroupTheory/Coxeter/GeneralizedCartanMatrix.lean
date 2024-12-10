/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

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
3. $k_{i, i'} \leq 0$ for $i \neq i'$.
4. If $m = M_{i, i'}$ is even, then $S_{m/2 - 1}(k_{i, i'} k_{i', i} - 2) = 0$, where $S$ refers to
  a Chebyshev $S$-polynomial (`Polynomial.Chebyshev.S`).
5. If $m = M_{i, i'}$ is odd, then
  $S_{(m-1)/2}(k_{i, i'} k_{i', i} - 2) + S_{(m-3)/2}(k_{i, i'} k_{i', i} - 2) = 0$.
6. For $0 \leq j \leq M_{i, i'} / 2 - 1$, we have $S_{j}(k_{i, i'} k_{i', i} - 2) \geq 0$.
7. If $M_{i, i'} = 0$, then $S_{j}(k_{i, i'} k_{i', i} - 2) \geq 0$ for all $j \geq 0$.
Generalized Cartan matrices can be used to define reflection representations of the Coxeter group
corresponding to the Coxeter matrix $M$. -/
@[mk_iff]
structure IsGeneralizedCartan {R : Type*} [OrderedCommRing R] (M : CoxeterMatrix B)
    (k : Matrix B B R) : Prop where
  diagonal i : k i i = 2
  eq_zero_iff i i' : k i i' = 0 ↔ M i i' = 2
  nonpos i i' (_ : i ≠ i') : k i i' ≤ 0
  s_eval_eq_zero_of_even i i' (j : ℤ) (_ : M i i' = 2 * j) :
    Polynomial.eval (k i i' * k i' i - 2) (S R (j - 1)) = 0
  s_eval_eq_zero_of_odd i i' (j : ℤ) (_ : M i i' = 2 * j + 1) :
    Polynomial.eval (k i i' * k i' i - 2) (S R (j - 1)) +
      Polynomial.eval (k i i' * k i' i - 2) (S R j) = 0
  s_eval_nonneg i i' (j : ℕ) (_ : 2 * j + 2 ≤ M i i') :
    0 ≤ Polynomial.eval (k i i' * k i' i - 2) (S R j)
  s_eval_nonneg' i i' (j : ℕ) (_ : M i i' = 0) :
    0 ≤ Polynomial.eval (k i i' * k i' i - 2) (S R j)

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
  nonpos i i' (_ : i ≠ i') : k i i' ≤ 0
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

theorem isRealGeneralizedCartan_of_isGeneralizedCartan (M : CoxeterMatrix B) (k : Matrix B B ℝ)
    (h : M.IsGeneralizedCartan k) : M.IsRealGeneralizedCartan k := by
  -- Collect hypotheses, writing them over ℂ instead of ℝ.
  have h₁ i i' (j : ℤ) (hj : M i i' = 2 * j) :
        Polynomial.eval ((k i i' * k i' i - 2 : ℝ) : ℂ) (S ℂ (j - 1)) = 0 := by
      simp_rw [← complex_ofReal_eval_S]
      exact_mod_cast h.s_eval_eq_zero_of_even i i' j hj
  have h₂ i i' (j : ℤ) (hj : M i i' = 2 * j + 1) :
      Polynomial.eval ((k i i' * k i' i - 2 : ℝ) : ℂ) (S ℂ (j - 1)) +
        Polynomial.eval ((k i i' * k i' i - 2 : ℝ) : ℂ) (S ℂ j) = 0 := by
    simp_rw [← complex_ofReal_eval_S]
    exact_mod_cast h.s_eval_eq_zero_of_odd i i' j hj
  have h₃ i i' (j : ℕ) (hj : 2 * j + 2 ≤ M i i') :
      0 ≤ (Polynomial.eval ((k i i' * k i' i - 2 : ℝ) : ℂ) (S ℂ j)).re := by
    simp_rw [← complex_ofReal_eval_S, Complex.ofReal_re]
    exact h.s_eval_nonneg i i' j hj
  have h₄ i i' (j : ℕ) (hii' : M i i' = 0) :
      0 ≤ (Polynomial.eval ((k i i' * k i' i - 2 : ℝ) : ℂ) (S ℂ j)).re := by
    simp_rw [← complex_ofReal_eval_S, Complex.ofReal_re]
    exact h.s_eval_nonneg' i i' j hii'
  constructor
  · show ∀ i, k i i = 2
    exact h.diagonal
  · show ∀ (i i'), k i i' = 0 ↔ M i i' = 2
    exact h.eq_zero_iff
  · show ∀ (i i'), i ≠ i' → k i i' ≤ 0
    exact h.nonpos
  · show ∀ (i i'), M.M i i' ≠ 0 → k i i' * k i' i = 4 * cos (π / ↑(M.M i i')) ^ 2
    intro i i' hii'
    specialize h₁ i i'
    specialize h₂ i i'
    specialize h₃ i i'
    specialize h₄ i i'
    -- Rewrite `k i i' * k i' i - 2` as `2 * Complex.cos θ` for some `θ : ℂ`.
    obtain ⟨θ, hθ⟩ := Complex.cos_surjective (((k i i' * k i' i - 2 : ℝ) : ℂ) / 2)
    have eq_two_mul_cos_theta : ((k i i' * k i' i - 2 : ℝ) : ℂ) = 2 * Complex.cos θ := by
      rw [hθ]
      ring
    simp_rw [eq_two_mul_cos_theta] at h₁ h₂ h₃ h₄
    /- Now we split into cases based on whether `M i i'` is equal to `1`, equal to `2`, or greater
    than or equal to `3`. -/
    obtain M_eq_one | M_eq_two | M_gt_two := show M i i' = 1 ∨ M i i' = 2 ∨ 3 ≤ M i i' by omega
    · /- If `M i i' = 1`, then `i = i'` by the definition of a Coxeter matrix, so
      `k i i' = k i' i = k i i = 2`, and we are done. -/
      have := M.off_diagonal i i'
      have : i = i' := by tauto
      simp only [← this, h.diagonal, diagonal, Nat.cast_one, div_one, cos_pi, even_two,
        Even.neg_pow, one_pow, mul_one]
      norm_num
    · -- If `M i i' = 2`, then we use `h.eq_zero_iff`.
      simp [M_eq_two, (h.eq_zero_iff i i').mpr M_eq_two]
    · -- If `M i i' > 1`, then we first claim that `cos θ` cannot be `1` or `-1`.
      have cos_θ_ne_one : Complex.cos θ ≠ 1 := by
        intro cos_θ_eq_one
        simp [cos_θ_eq_one, show 2 * 1 = 2 by norm_num] at h₁ h₂
        obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (M.M i i')
        · have := h₁ j (mod_cast hj)
          omega
        · have := h₂ j (mod_cast hj)
          norm_cast at this
      have cos_θ_ne_neg_one : Complex.cos θ ≠ -1 := by
        intro cos_θ_eq_neg_one
        simp [cos_θ_eq_neg_one, show 2 * 1 = 2 by norm_num] at h₁ h₂
        obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (M.M i i')
        · have := h₁ j (mod_cast hj)
          omega
        · have := h₂ j (mod_cast hj)
          simp [Int.negOnePow_sub, ← neg_mul, ← add_mul] at this
      -- Now, we claim that the angle `θ` is an integer multiple of `2 * π / M i i'`.
      have θ_mul_Mii'_eq : ∃ (ℓ : ℤ), θ * M i i' = ℓ * (2 * π) := by
        -- We use the hypothesis `h₁` or `h₂`, depending on whether `M i i'` is even or odd.
        obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (M.M i i')
        · have eval_s_eq_zero := h₁ j (mod_cast hj)
          have eval_s_mul_sin_eq_zero := congrArg (· * Complex.sin θ) eval_s_eq_zero
          simp only [S_two_mul_complex_cos, zero_mul] at eval_s_mul_sin_eq_zero
          push_cast at eval_s_mul_sin_eq_zero
          simp only [sub_add_cancel] at eval_s_mul_sin_eq_zero
          -- If `M i i' = 2 * j` is even, then we conclude that `sin (j * θ) = 0`.
          guard_hyp eval_s_mul_sin_eq_zero : Complex.sin (j * θ) = 0
          -- It follows that `j * θ` is an integer multiple of `π`, so we have proved our claim.
          obtain ⟨ℓ, hℓ⟩ := Complex.sin_eq_zero_iff.mp eval_s_mul_sin_eq_zero
          use ℓ
          rw [mul_left_comm, ← hℓ, hj]
          push_cast
          ring
        · have eval_s_eq_zero := h₂ j (mod_cast hj)
          have eval_s_mul_sin_eq_zero := congrArg (· * Complex.sin θ) eval_s_eq_zero
          simp_rw [add_mul, S_two_mul_complex_cos, zero_mul] at eval_s_mul_sin_eq_zero
          push_cast at eval_s_mul_sin_eq_zero
          simp_rw [sub_add_cancel] at eval_s_mul_sin_eq_zero
          /- If `M i i' = 2 * j + 1` is odd, then we conclude that
          `sin (j * θ) + sin ((j + 1) * θ) = 0`. -/
          guard_hyp eval_s_mul_sin_eq_zero : Complex.sin (j * θ) + Complex.sin ((j + 1) * θ) = 0
          have : Complex.sin (-j * θ) = Complex.sin ((j + 1) * θ) := by
            rw [add_eq_zero_iff_eq_neg'.mp eval_s_mul_sin_eq_zero, neg_mul, Complex.sin_neg]
          /- It follows that either `j * θ + (j + 1) * θ` is a multiple of `2 * π`, or that
          `(j + 1) * θ - j * θ` is an odd multiple of `π`. In the former case, we are done.
          In the latter case, we reach a contradiction. -/
          obtain ⟨ℓ, hℓ | hℓ⟩ := Complex.sin_eq_sin_iff.mp this
          · use ℓ
            rw [hj]
            push_cast at hℓ ⊢
            linear_combination hℓ
          · have θ_eq_odd_mul_pi : θ = (2 * ℓ + 1) * π := by linear_combination hℓ
            have cos_θ_eq_neg_one : Complex.cos θ = -1 := by
              convert Complex.cos_int_mul_two_pi_add_pi ℓ
              linear_combination θ_eq_odd_mul_pi
            contradiction
      obtain ⟨ℓ, hℓ⟩ := θ_mul_Mii'_eq
      /- We get `θ = ℓ * (2 * π) / M i i'` for some integer `ℓ`. We may replace `ℓ` in this equation
      with a natural number `ℓ' = Int.natAbs (Int.bmod ℓ (M i i'))` without changing the value of
      `cos θ`.-/
      apply eq_div_of_mul_eq (mod_cast hii') at hℓ
      let ℓ' := Int.natAbs (Int.bmod ℓ (M i i'))
      let θ' := ℓ' * (2 * π) / (M i i')
      have cos_θ'_eq_cos_θ : Real.cos θ' = Complex.cos θ := by
        unfold θ' ℓ'
        rw [hℓ, Int.cast_natAbs, Int.cast_abs, mul_div_assoc,
          ← abs_eq_self.mpr (show (2 * π) / M i i' ≥ 0 by positivity), ← abs_mul, cos_abs,
          Int.bmod_def, Int.emod_def]
        norm_cast
        split
        · push_cast
          rw [sub_mul, mul_comm (M i i' : ℝ), mul_assoc, mul_div_cancel₀ _ (mod_cast hii'),
            cos_sub_int_mul_two_pi, ← mul_div_assoc]
        · push_cast
          rw [sub_mul, sub_mul, mul_comm (M i i' : ℝ), mul_assoc, mul_div_cancel₀ _ (mod_cast hii'),
            cos_sub_two_pi, cos_sub_int_mul_two_pi, ← mul_div_assoc]
      -- Now write all the hypotheses in terms of `θ'` instead of `θ`.
      simp_rw [← cos_θ'_eq_cos_θ] at h₁ h₂ h₃ h₄ eq_two_mul_cos_theta cos_θ_ne_one cos_θ_ne_neg_one
      norm_cast at h₁ h₂ h₃ h₄ eq_two_mul_cos_theta cos_θ_ne_one cos_θ_ne_neg_one
      -- Now, we will put bounds on `ℓ'`. Namely, we will prove that it is less than `M i i' / 2`.
      have two_mul_ℓ'_ne_Mii' : 2 * ℓ' ≠ M i i' := by
        intro two_mul_ℓ'_eq_Mii'
        unfold θ' at cos_θ_ne_neg_one
        rw_mod_cast [← mul_assoc, mul_comm _ 2, two_mul_ℓ'_eq_Mii',
          mul_div_cancel_left₀ _ (mod_cast hii')] at cos_θ_ne_neg_one
        simp at cos_θ_ne_neg_one
      have two_mul_ℓ'_lt_Mii' : 2 * ℓ' < M i i' := by
        unfold ℓ'
        have := Int.bmod_le (x := ℓ) (Nat.zero_lt_of_ne_zero hii')
        have := Int.le_bmod (x := ℓ) (Nat.zero_lt_of_ne_zero hii')
        omega
      -- We claim that `ℓ'` is positive,
      have ℓ'_pos : 0 < ℓ' := by
        apply (Nat.eq_zero_or_pos ℓ').resolve_left
        intro ℓ'_eq_zero
        unfold θ' at cos_θ_ne_one
        simp [ℓ'_eq_zero] at cos_θ_ne_one
      -- This implies that `sin θ'` is positive.
      have sin_θ'_pos : 0 < sin θ' := by
        unfold θ'
        apply sin_pos_of_pos_of_lt_pi
        · positivity
        · rw [div_lt_iff₀ (by positivity), ← mul_assoc, mul_comm π, mul_comm _ 2]
          apply mul_lt_mul_of_pos_right
          · exact_mod_cast two_mul_ℓ'_lt_Mii'
          · exact pi_pos
      -- If `ℓ' = 1`, we are done, so assume that `ℓ' ≠ 1`. This implies that `ℓ` is at least `2`.
      suffices ℓ' = 1 by
        simp only [eq_add_of_sub_eq eq_two_mul_cos_theta, this, Nat.cast_one, one_mul, θ',
          mul_div_assoc, cos_two_mul]
        ring
      by_contra ℓ'_ne_one
      have ℓ'_ge_two : 2 ≤ ℓ' := by omega
      -- Now we claim that we get a contradiction from `h₃` (i.e. `s_eval_nonneg`)
      exfalso
      let j := M i i' / (2 * ℓ')
      have h₂j : 2 * j + 2 ≤ M i i' := by
        unfold j
        calc
          2 * (M i i' / (2 * ℓ')) + 2
          _ = 2 * (M i i' / (ℓ' * 2)) + 2 := by rw [mul_comm 2 ℓ']
          _ = 2 * (M i i' / ℓ' / 2) + 2   := by rw [Nat.div_div_eq_div_mul]
          _ ≤ M i i' / ℓ' + 2             := add_le_add_right (Nat.mul_div_le _ _) _
          _ = (M i i' + 2 * ℓ') / ℓ'      := by rw [Nat.add_mul_div_right]; exact ℓ'_pos
          _ ≤ M i i'                      := by
            rw [Nat.div_le_iff_le_mul_add_pred ℓ'_pos]
            zify
            rw [Int.natCast_sub ℓ'_pos]
            push_cast
            have hm : 0 ≤ (M i i' - 3 : ℤ) := sub_nonneg_of_le M_gt_two



      have h₃j : M i i' < (j + 1) * (2 * ℓ') := by
        unfold j
        rw [Nat.sub_add_cancel h₁j]
        apply Nat.succ_le_iff.mp


      have := h₃ j h₂j





  · sorry

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

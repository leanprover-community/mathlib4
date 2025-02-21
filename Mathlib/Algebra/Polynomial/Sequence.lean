/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
import Mathlib.Algebra.Ring.Regular
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

Generalize linear independence to:
  * `IsCancelAdd` semirings
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

open Submodule
open scoped Function

variable (R : Type*)

namespace Polynomial

instance [Semiring R] [IsCancelAdd R] : IsCancelAdd (Polynomial R) := by
  refine @AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _ _ (.mk fun p q r h ↦ ?_)
  ext n
  simp_rw [ext_iff, coeff_add] at h
  exact (add_right_inj _).1 (h n)

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  /-- The `i`'th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`'th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems' i`. -/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦  ℕ → R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

/-- `S i` has degree `i`. -/
@[simp]
lemma degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

/-- `S i` has `natDegree` `i`. -/
@[simp]
lemma natDegree_eq (i : ℕ) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some <| S.degree_eq i

/-- No polynomial in the sequence is zero. -/
@[simp]
lemma ne_zero (i : ℕ) : S i ≠ 0 := degree_ne_bot.mp <| by simp [S.degree_eq i]

/-- `S i` has strictly monotone degree. -/
lemma degree_strictMono : StrictMono <| degree ∘ S := fun _ _  ↦ by simp

/-- `S i` has strictly monotone natural degree. -/
lemma natDegree_strictMono : StrictMono <| natDegree ∘ S := fun _ _  ↦ by simp

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
protected lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ :=
  eq_top_iff'.mpr fun P ↦ by
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases p_ne_zero : P = 0
    · simp [p_ne_zero]

    obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n

    let head := P.leadingCoeff • u • S n
    let tail := P - head

    have head_mem_span : head ∈ span R (Set.range S) := by
      have in_span : S n ∈ span R (Set.range S) := subset_span (by simp)
      have smul_span := smul_mem (span R (Set.range S)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span

    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    refine sub_mem_iff_left _ head_mem_span |>.mp <| ih tail.natDegree ?_ _ rfl

    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular _ <| IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right

    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff

    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n).isRegular.right
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
        ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq

    have head_nonzero : head ≠ 0 := by
      by_cases n_eq_zero : n = 0
      · rw [n_eq_zero, ← coeff_natDegree, natDegree_eq] at rightinv
        dsimp [head]
        rwa [n_eq_zero, eq_C_of_natDegree_eq_zero <| S.natDegree_eq 0,
          smul_C, smul_eq_mul, map_mul, ← C_mul, rightinv, smul_C, smul_eq_mul,
          mul_one, C_eq_zero, leadingCoeff_eq_zero]
      · apply head.ne_zero_of_degree_gt
        rw [← head_degree_eq]
        exact natDegree_pos_iff_degree_pos.mp (by omega)

    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree, degree_eq_natDegree head_nonzero] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rwa [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]

    refine natDegree_lt_iff_degree_lt tail_eq_zero |>.mpr ?_
    have tail_degree_lt := P.degree_sub_lt head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

section NoZeroDivisors

variable [NoZeroDivisors R]

section Test

variable {R : Type*} [Semiring R] [NoZeroDivisors R]
  (S : Sequence R)

@[simp]
lemma _root_.Finsupp.linearCombination_support_eq_empty {α M R : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (v : α → M) {l : α →₀ R} (hl : l.support = ∅) :
    l.linearCombination R v = 0 := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [hl] at ha
  contradiction

lemma nat_deg {a : ℕ →₀ R} : (a.linearCombination R S).natDegree = a.support.sup id := by
  obtain ha | ha := Finset.eq_empty_or_nonempty a.support
  · simp [Finsupp.support_eq_empty.1 ha]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have : a.support.sup id = a.support.sup (fun i ↦ ((a i) • (S i)).natDegree) := by
    apply Finset.sup_congr rfl
    intro i hi
    rw [natDegree_smul]
    · simp
    · exact Finsupp.mem_support_iff.1 hi
  rw [this]
  apply Polynomial.natDegree_sum_eq_of_disjoint
  intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
  have zgx : a x ≠ 0 := (smul_ne_zero_iff.mp hx).1
  have zgy : a y ≠ 0 := (smul_ne_zero_iff.mp hy).1
  simp only [ne_eq, Function.comp_apply]
  rw [natDegree_smul _ zgx, natDegree_smul _ zgy]
  simpa


lemma linearIndependent {R : Type*} [Semiring R] [IsCancelAdd R] [NoZeroDivisors R]
    (S : Sequence R) : LinearIndependent R S := by
  intro a b h
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
  have lol : a.support.sup id = b.support.sup id := sorry
  have has : a.support.Nonempty := sorry
  have hbs : b.support.Nonempty := sorry
  generalize hn : a.support.sup id = n
  induction n generalizing a b with
  | zero =>
    have as : a.support = {0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      constructor
      · nth_rw 1 [← hn, ← a.support.image_id, ← Finset.mem_coe, Finset.coe_image]
        apply Finset.sup_mem_of_nonempty
        exact has
      · intro x hx
        apply le_zero_iff.1
        rw [← hn, ← id_eq x]
        exact Finset.le_sup hx
    have bs : b.support = {0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      constructor
      · nth_rw 1 [← hn, lol, ← b.support.image_id, ← Finset.mem_coe, Finset.coe_image]
        apply Finset.sup_mem_of_nonempty
        exact hbs
      · intro x hx
        apply le_zero_iff.1
        rw [← hn, lol, ← id_eq x]
        exact Finset.le_sup hx
    rw [as, bs, Finset.sum_singleton, Finset.sum_singleton] at h
    ext i
    obtain rfl | hi := eq_or_ne i 0


end Test

/-- Polynomials in a polynomial sequence are linearly independent. -/
lemma linearIndependent' :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i ↦ (g i • S i).degree)
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i ∈ s ∧ g i • S i ≠ 0}.Pairwise (Ne on fun i ↦ (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x ≠ 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y ≠ 0 := (smul_ne_zero_iff.mp hy).1
    have rx : IsRightRegular (S x).leadingCoeff := isRegular_of_ne_zero (by simp) |>.right
    have ry : IsRightRegular (S y).leadingCoeff := isRegular_of_ne_zero (by simp) |>.right
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S i).degree) = n := exists_eq'
  refine degree_ne_bot.mp ?_ eqzero |>.elim
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
  exact hsum.trans hn |>.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| eq_top_iff.mp <| S.span hCoeff

/-- The `i`'th basis vector is the `i`'th polynomial in the sequence. -/
@[simp]
lemma basis_eq_self  (i : ℕ) : S.basis hCoeff i = S i := Basis.mk_apply _ _ _

/-- Basis elements have strictly monotone degree. -/
lemma basis_degree_strictMono : StrictMono <| degree ∘ (S.basis hCoeff) := fun _ _  ↦ by simp

/-- Basis elements have strictly monotone natural degree. -/
lemma basis_natDegree_strictMono : StrictMono <| natDegree ∘ (S.basis hCoeff) := fun _ _  ↦ by simp

end NoZeroDivisors

end Ring

end Sequence

end Polynomial

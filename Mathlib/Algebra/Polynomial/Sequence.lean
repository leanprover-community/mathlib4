/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Order.Interval.Set.SuccPred
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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

@[expose] public section

open Module Submodule
open scoped Function

variable (R : Type*)

namespace Polynomial

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  /-- The `i`-th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`-th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems' i`. -/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦ ℕ → R[X]) := ⟨Sequence.elems'⟩

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
lemma degree_strictMono : StrictMono <| degree ∘ S := fun _ _ ↦ by simp

/-- `S i` has strictly monotone natural degree. -/
lemma natDegree_strictMono : StrictMono <| natDegree ∘ S := fun _ _ ↦ by simp

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- The first `m` polynomials of a polynomial sequence span all polynomials of degree `< m` if their
    leading coefficients are units. -/
lemma span_degreeLT {m : ℕ} (hCoeff : ∀ i < m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iio m) = degreeLT R m := by
  apply span_eq_of_le
  · intro P hP
    obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hP
    rw [SetLike.mem_coe, Polynomial.mem_degreeLT, S.degree_eq i, Nat.cast_lt]
    exact Set.mem_Iio.mp hi
  intro P hP
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases! p_ne_zero : P = 0
    · simp [p_ne_zero]
    have hn : n < m := by
      rw [Polynomial.mem_degreeLT] at hP
      have := Polynomial.degree_eq_natDegree p_ne_zero
      aesop
    -- let u be the inverse of `S n`'s leading coefficient
    obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n hn
    -- We'll show `P` is the difference of two terms in the span:
    --   a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    --   and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head ∈ span R (S '' Set.Iio m) := by
      have in_span : S n ∈ span R (S '' Set.Iio m) := subset_span ⟨n, by simp [hn], rfl⟩
      have smul_span := smul_mem (span R (S '' Set.Iio m)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
    apply sub_mem_iff_left _ head_mem_span |>.mp
    -- so let's prove the tail has degree less than `n`
    suffices tail.degree < n by
      refine ih tail.natDegree ((natDegree_lt_iff_degree_lt tail_eq_zero).mpr this) ?_ rfl
      grw [(Nat.cast_lt (α := WithBot ℕ)).mpr hn] at this
      rwa [Polynomial.mem_degreeLT]
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular, IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n hn).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
      ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
    have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree <| by
      grind [degree_eq_bot]
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree p_ne_zero, head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rw [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

/-- The first `m + 1` polynomials of a polynomial sequence span all polynomials of degree `≤ m` if
    their leading coefficients are units. -/
lemma span_degreeLE {m : ℕ} (hCoeff : ∀ i ≤ m, IsUnit (S i).leadingCoeff) :
    span R (S '' Set.Iic m) = degreeLE R m := by
  rw [← Set.Iio_succ_eq_Iic, span_degreeLT _ (fun i hi => hCoeff i (Order.lt_succ_iff.mp hi))]
  simp [← Polynomial.degreeLT_succ_eq_degreeLE]

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
protected lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ := by
  rw [eq_top_iff']
  intro P
  by_cases! p_ne_zero : P = 0
  · simp [p_ne_zero]
  suffices P ∈ span R (S '' Set.Iio (P.natDegree + 1)) from (span_mono (by simp)) this
  rw [span_degreeLT _ (by grind), Polynomial.mem_degreeLT, ← natDegree_lt_iff_degree_lt p_ne_zero]
  simp

section IsDomain

variable [IsDomain R]

/-- Polynomials in a polynomial sequence are linearly independent. -/
lemma linearIndependent :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i ↦ (g i • S i).degree)
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i ∈ s ∧ g i • S i ≠ 0}.Pairwise (Ne on fun i ↦ (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x ≠ 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y ≠ 0 := (smul_ne_zero_iff.mp hy).1
    have rx : IsRightRegular (S x).leadingCoeff := IsRegular.of_ne_zero (by simp) |>.right
    have ry : IsRightRegular (S y).leadingCoeff := IsRegular.of_ne_zero (by simp) |>.right
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S i).degree) = n := exists_eq'
  refine degree_ne_bot.mp ?_ eqzero |>.elim
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
  exact hsum.trans hn |>.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| eq_top_iff.mp <| S.span hCoeff

/-- The `i`-th basis vector is the `i`-th polynomial in the sequence. -/
@[simp]
lemma basis_eq_self (i : ℕ) : S.basis hCoeff i = S i := Basis.mk_apply _ _ _

/-- Basis elements have strictly monotone degree. -/
lemma basis_degree_strictMono : StrictMono <| degree ∘ (S.basis hCoeff) := fun _ _ ↦ by simp

/-- Basis elements have strictly monotone natural degree. -/
lemma basis_natDegree_strictMono : StrictMono <| natDegree ∘ (S.basis hCoeff) := fun _ _ ↦ by simp

end IsDomain

end Ring

end Sequence

end Polynomial

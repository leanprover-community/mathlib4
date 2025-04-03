/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Equivalence of two-sided ideals of A and Mₙ(A)

In this file, we show that the two-sided ideals of `A` corresponds bijectively to that of `Mₙ(A)`.

## Main results

* `TwoSidedIdeal.equivRingConMatrix` : The equivalence between the two-sided ideals of `A` and
  `Mₙ(A)` where sends `I ≤ A` to `Mₙ(I)` and `J ≤ Mₙ(A)` to `{x₀₀ | x ∈ J}`.
* `TwoSidedIdeal.OrderEquivMatrix` : The order isomorphism between the two-sided ideals of `A`
  and `Mₙ(A)`.
-/

variable (A : Type*) [Ring A]

open BigOperators Matrix MulOpposite

local notation "M[" ι "," R "]" => Matrix ι ι R

namespace TwoSidedIdeal

variable (ι : Type) [Fintype ι]

/--
If `I` is a two-sided-ideal of `A`, then `Mₙ(I) := {(xᵢⱼ) | ∀ i j, xᵢⱼ ∈ I}` is a two-sided-ideal of
`Mₙ(A)`.
-/
@[simps]
def mapMatrix (I : TwoSidedIdeal A) : TwoSidedIdeal M[ι, A] := .mk
{
  r := fun X Y => ∀ i j, I.ringCon (X i j) (Y i j)
  iseqv :=
  { refl := fun X i j ↦ I.ringCon.refl (X i j)
    symm := fun h i j ↦ I.ringCon.symm (h i j)
    trans := fun h1 h2 i j ↦ I.ringCon.trans (h1 i j) (h2 i j) }
  mul' := by
    intro _ _ _ _ h h' i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [TwoSidedIdeal.rel_iff, ← Finset.sum_sub_distrib]
    apply I.finsetSum_mem
    rintro k -
    rw [← TwoSidedIdeal.rel_iff]
    apply I.ringCon.mul (h _ _) (h' _ _)
  add' := fun {X X' Y Y'} h h' i j ↦ by
    simpa only [Matrix.add_apply] using I.ringCon.add (h _ _) (h' _ _)
}

@[simp] lemma mem_mapMatrix (I : TwoSidedIdeal A) (x) : x ∈ I.mapMatrix A ι ↔
    ∀ i j, x i j ∈ I :=
  Iff.rfl

variable [Inhabited ι]

/-- If `I` is an two-sided ideal of `Mₙ(A)`, then `{M₀₀| M ∈ I}` is a two-sided ideal of `A`. -/
@[simps!]
def fromMatrix (I : TwoSidedIdeal M[ι, A]) :
    TwoSidedIdeal A :=
  .mk'
    ((fun (x : M[ι, A]) ↦ x default default) '' I)
    ⟨0, I.zero_mem, rfl⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, I.add_mem hx hy, rfl⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, I.neg_mem hx, rfl⟩)
    (by
      classical
      rintro x _ ⟨y, hy, rfl⟩
      exact ⟨Matrix.diagonal (fun _ ↦ x) * y, I.mul_mem_left _ _ hy, by simp⟩)
    (by
      classical
      rintro _ y ⟨x, hx, rfl⟩
      exact ⟨x * Matrix.diagonal (fun _ ↦ y), I.mul_mem_right _ _ hx, by simp⟩)

variable [DecidableEq ι]

/--
The two-sided-ideals of `A` corresponds bijectively to that of `Mₙ(A)`.
Given an ideal `I ≤ A`, we send it to `Mₙ(I)`.
Given an ideal `J ≤ Mₙ(A)`, we send it to `{x₀₀ | x ∈ J}`.
-/
@[simps]
def equivRingConMatrix : TwoSidedIdeal A ≃ TwoSidedIdeal M[ι, A] where
  toFun I := I.mapMatrix A ι
  invFun J := J.fromMatrix A
  right_inv J := SetLike.ext fun x ↦ by
    simp only [mem_mapMatrix]
    constructor
    · intro h
      choose y hy1 hy2 using h
      rw [Matrix.matrix_eq_sum_stdBasisMatrix x]
      refine J.finsetSum_mem _ _ fun i _ ↦ J.finsetSum_mem _ _ fun j _ ↦ ?_
      suffices
          stdBasisMatrix i j (x i j) =
          stdBasisMatrix i default 1 * y i j * stdBasisMatrix default j 1 by
        rw [this]
        exact J.mul_mem_right _ _ (J.mul_mem_left _ _ <| hy1 _ _)
      ext a b
      by_cases hab : a = i ∧ b = j
      · rcases hab with ⟨ha, hb⟩
        subst ha hb
        simp only [StdBasisMatrix.apply_same, StdBasisMatrix.mul_right_apply_same,
          StdBasisMatrix.mul_left_apply_same, one_mul, mul_one]
        specialize hy2 a b
        simp only [sub_zero] at hy2
        exact hy2.symm
      · conv_lhs =>
          dsimp [stdBasisMatrix]
          rw [if_neg (by tauto)]
        rw [not_and_or] at hab
        rcases hab with ha | hb
        · rw [mul_assoc, Matrix.StdBasisMatrix.mul_left_apply_of_ne (h := ha)]
        · rw [Matrix.StdBasisMatrix.mul_right_apply_of_ne (hbj := hb)]
    · intro hx i j
      refine ⟨stdBasisMatrix default i 1 * x * stdBasisMatrix j default 1,
        J.mul_mem_right _ _ (J.mul_mem_left _ _ hx), ?_⟩
      simp only [StdBasisMatrix.mul_right_apply_same, StdBasisMatrix.mul_left_apply_same, one_mul,
        mul_one, sub_zero]
  left_inv I := SetLike.ext fun x ↦ by
    simp only
    constructor
    · intro h
      choose y hy1 hy2 using h
      simp only [sub_zero] at hy2
      exact hy2 ▸ hy1 _ _
    · intro h
      exact ⟨of fun _ _ => x, by simp [h], by simp⟩

/--
`equivRingConMatrix` preserves order of two-sided ideals since if `I ≤ J` then
clearly `Mₙ(I)` is a subset of `Mₙ(J)`.
-/
def OrderEquivMatrix : TwoSidedIdeal A ≃o TwoSidedIdeal M[ι, A] where
__ := TwoSidedIdeal.equivRingConMatrix A _
map_rel_iff' {I J} := by
  simp only [equivRingConMatrix_apply, TwoSidedIdeal.le_iff]
  constructor
  · intro h x hx
    specialize @h (of fun _ _ => x)
      (by simp only [SetLike.mem_coe, mem_mapMatrix, of_apply]; intros; exact hx)
    simp only [SetLike.mem_coe, mem_mapMatrix, of_apply] at h
    exact h default default
  · intro h X hX i j
    exact h <| hX i j

end TwoSidedIdeal

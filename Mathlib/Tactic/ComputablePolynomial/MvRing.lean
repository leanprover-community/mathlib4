/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvToPoly

/-!
# `MvSparsePoly`: multiplicativity of `toPoly` and the `CommRing` and `Algebra` instances

`toPoly` preserves multiplication (via the `flatMap` expansion of `mulCore`), giving the
`CommRing` and `Algebra R` instances on `MvSparsePoly R nvars`, the constant ring hom `CHom`,
the bridge `toPoly_X`, and decidable equality.
-/

@[expose] public section

variable {nvars : ℕ}

namespace MvSparsePoly

open MvPolynomial

variable {R : Type} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
theorem toPolyCore_perm {l1 l2 : List (MvDegrees nvars × R)} (h : l1.Perm l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => dsimp [toPolyCore]; rw [ih]
  | swap x y l => dsimp [toPolyCore]; ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

omit [DecidableEq R] in
/-- `mergeSort` is a permutation, so it preserves the polynomial. -/
theorem toPolyCore_mergeSort (l : List (MvDegrees nvars × R))
  (r : (MvDegrees nvars × R) → (MvDegrees nvars × R) → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l :=
  toPolyCore_perm (l.mergeSort_perm r)

omit [DecidableEq R] in
theorem toPolyCore_dedupList : ∀ (l : List (MvDegrees nvars × R)),
    toPolyCore (dedupList l) = toPolyCore l
  | [] => by simp [dedupList, toPolyCore]
  | [x] => by simp [dedupList, toPolyCore]
  | (i, a) :: (j, b) :: xs => by
      unfold dedupList
      split
      · next heq =>
        subst heq
        rw [toPolyCore_dedupList ((i, a + b) :: xs)]
        dsimp [toPolyCore]
        rw [map_add]
        ring
      · next hneq =>
        dsimp [toPolyCore]
        rw [toPolyCore_dedupList ((j, b) :: xs)]
        simp only [toPolyCore]

/-- The master bridge: `toPoly (ofList l) = toPolyCore l`. -/
theorem toPoly_ofList (l : List (MvDegrees nvars × R)) :
    toPoly (ofList l) = toPolyCore l := by
  unfold toPoly ofList ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

omit [DecidableEq R] in
/-- Multiplying a term list by a single monomial `(i, a)`. -/
theorem toPolyCore_monomial_mul (l : List (MvDegrees nvars × R)) (i : MvDegrees nvars) (a : R) :
    toPolyCore (l.map fun ⟨j, b⟩ => (i + j, a * b)) =
    (MvPolynomial.monomial (MvDegrees.toFinsupp i) a) * toPolyCore l := by
  induction l with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨j, b⟩
    dsimp [toPolyCore]
    rw [mul_add, ← ih]
    congr 1
    rw [MvPolynomial.monomial_mul, toFinsupp_add, mul_comm a b, add_comm]

theorem toPolyCore_ofList_terms (l : List (MvDegrees nvars × R)) :
    toPolyCore (ofList l).terms = toPolyCore l := by
  unfold ofList ofSortedList
  dsimp
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

omit [DecidableEq R] in
/-- `toPolyCore` distributes over list append. -/
theorem toPolyCore_append (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    dsimp [toPolyCore]
    rw [ih, add_assoc]

omit [DecidableEq R] in
/-- `flatMap` form of `toPolyCore_monomial_mul`. -/
theorem toPolyCore_monomial_mul_flatMap (l : List (MvDegrees nvars × R))
      (i : MvDegrees nvars) (a : R) :
    toPolyCore (l.flatMap fun x => [(i + x.1, a * x.2)]) =
    (MvPolynomial.monomial (MvDegrees.toFinsupp i) a) * toPolyCore l := by
  induction l with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    change (MvPolynomial.monomial (MvDegrees.toFinsupp (i + hd.1))) (a * hd.2) +
           toPolyCore (tl.flatMap fun x => [(i + x.1, a * x.2)]) = _
    rw [ih]
    erw [mul_add]
    congr 1
    rw [MvPolynomial.monomial_mul, toFinsupp_add, mul_comm a hd.2, add_comm]

omit [DecidableEq R] in
/-- The product of two term lists, expanded via `flatMap`, computes the polynomial product. -/
theorem toPolyCore_mul_flatMap (l1 l2 : List (MvDegrees nvars × R)) :
    toPolyCore (l1.flatMap fun x => l2.flatMap fun y => [(x.1 + y.1, x.2 * y.2)]) =
    toPolyCore l1 * toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    change toPolyCore ((l2.flatMap fun y => [(hd.1 + y.1, hd.2 * y.2)]) ++
                       (tl.flatMap fun x => l2.flatMap fun y => [(x.1 + y.1, x.2 * y.2)])) = _
    rw [toPolyCore_append, toPolyCore_monomial_mul_flatMap, ih]
    dsimp [toPolyCore]
    rw [add_mul]

lemma toPoly_mul (a b : MvSparsePoly R nvars) :
    toPoly (a * b) = toPoly a * toPoly b := by
  unfold toPoly
  dsimp [HMul.hMul, Mul.mul, mulCore]
  rw [toPolyCore_ofList_terms]
  exact toPolyCore_mul_flatMap a.terms b.terms

instance : CommRing (MvSparsePoly R nvars) where
  add := (·+·)
  zero := 0
  zero_add := poly_zero_add
  add_zero := poly_add_zero
  add_comm := poly_add_comm
  neg := (-·)
  neg_add_cancel := poly_add_left_neg
  mul := (·*·)
  one := 1
  zero_mul := poly_zero_mul
  mul_zero := poly_mul_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  natCast n := nsmulRec n 1
  natCast_zero := rfl
  natCast_succ := by intros; rfl
  zsmul_neg' := by intros; rfl
  add_assoc a b c := toPoly_injective (by simp only [toPoly_add, add_assoc])
  mul_assoc a b c := toPoly_injective (by simp only [toPoly_mul, mul_assoc])
  mul_comm a b := toPoly_injective (by simp only [toPoly_mul, mul_comm])
  left_distrib a b c := toPoly_injective (by simp only [toPoly_add, toPoly_mul, left_distrib])
  right_distrib a b c := toPoly_injective (by simp only [toPoly_add, toPoly_mul, right_distrib])
  one_mul a := toPoly_injective (by simp only [toPoly_mul, toPoly_one, one_mul])
  mul_one a := toPoly_injective (by simp only [toPoly_mul, toPoly_one, mul_one])

omit [DecidableEq R] in
lemma toPoly_zero : toPoly (0 : MvSparsePoly R nvars) = 0 := rfl

/-- The constant-polynomial inclusion `R → MvSparsePoly R nvars` as a ring homomorphism. -/
def CHom : R →+* MvSparsePoly R nvars where
  toFun := C
  map_zero' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_zero, map_zero]
  map_one' := by
    apply toPoly_injective
    simp only [toPoly_C, toPoly_one, map_one]
  map_add' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_add, toPoly_C, map_add]
  map_mul' := by
    intro x y
    apply toPoly_injective
    simp only [toPoly_mul, toPoly_C, map_mul]

instance : Algebra R (MvSparsePoly R nvars) where
  smul r p := C r * p
  algebraMap := CHom
  commutes' r p := mul_comm (C r) p
  smul_def' _ _ := rfl


lemma toFinsupp_singleDegree (v : Fin nvars) :
    MvDegrees.toFinsupp (singleDegree v) = Finsupp.single v 1 := by
  ext i
  rw [Finsupp.single_apply]
  unfold MvDegrees.toFinsupp singleDegree
  simp only [Finsupp.onFinset_apply]
  rw [Fin.getElem_fin, ← Array.getElem_toList]
  simp only [List.getElem_set, List.getElem_replicate]
  by_cases h : v = i
  · subst h; simp
  · rw [if_neg h]
    split
    · rename_i hc
      exact absurd (Fin.ext (show (v : ℕ) = (i : ℕ) by omega)) h
    · rfl

@[simp]
theorem toPoly_X (v : Fin nvars) :
    (X v : MvSparsePoly R nvars).toPoly = MvPolynomial.X v := by
  unfold X toPoly ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero]
  simp only [toPolyCore, add_zero]
  rw [toFinsupp_singleDegree]
  rfl

instance : DecidableEq (MvSparsePoly R nvars) := fun a b =>
  decidable_of_iff' (a.terms = b.terms) (MvSparsePoly.ext_iff ..)

end MvSparsePoly

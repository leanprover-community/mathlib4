/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.OfList

/-!
# `SparsePoly`: multiplication and the `CommRing` and `Algebra` instances

`toPoly` is shown to preserve `1`, multiplication and negation, and `SparsePoly R` is given its
`CommRing` and `Algebra R` instances, with `CHom : R →+* SparsePoly R` the constant ring hom.
-/

@[expose] public section

namespace SparsePoly

open Polynomial

variable {R : Type} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
theorem toPolyCore_append (l1 l2 : List (ℕ × R)) :
    toPolyCore (l1 ++ l2) = toPolyCore l1 + toPolyCore l2 := by
  induction l1 with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    calc
      toPolyCore ((i, a) :: tl ++ l2)
          = Polynomial.C a * Polynomial.X ^ i + toPolyCore (tl ++ l2) := by
              simp [List.cons_append, toPolyCore]
      _ = Polynomial.C a * Polynomial.X ^ i + (toPolyCore tl + toPolyCore l2) := by
            rw [ih]
      _ = toPolyCore ((i, a) :: tl) + toPolyCore l2 := by
            simp [toPolyCore, add_assoc]

omit [DecidableEq R] in
theorem toPolyCore_perm {l1 l2 : List (ℕ × R)} (h : List.Perm l1 l2) :
    toPolyCore l1 = toPolyCore l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    rcases x with ⟨i, a⟩
    dsimp only [toPolyCore]
    rw [ih]
  | swap x y l =>
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    dsimp only [toPolyCore]
    ring
  | trans _ _ ih1 ih2 =>
    exact Eq.trans ih1 ih2

omit [DecidableEq R] in
theorem toPolyCore_mergeSort (l : List (ℕ × R)) (r : ℕ × R → ℕ × R → Bool) :
    toPolyCore (l.mergeSort r) = toPolyCore l :=
  toPolyCore_perm (List.mergeSort_perm l r)

omit [DecidableEq R] in
theorem toPolyCore_dedupList : ∀ (l : List (ℕ × R)),
    toPolyCore (dedupList l) = toPolyCore l
  | [] => by
    simp [dedupList, toPolyCore]
  | [(i, a)] => by
    simp [dedupList, toPolyCore]
  | (i, a) :: (j, b) :: xs => by
    unfold dedupList
    split
    · next heq =>
      subst heq
      rw [toPolyCore_dedupList ((i, a + b) :: xs)]
      dsimp only [toPolyCore]
      rw [map_add, add_mul]
      ring
    · dsimp only [toPolyCore]
      rw [toPolyCore_dedupList ((j, b) :: xs)]
      simp [toPolyCore]

theorem toPoly_ofList (l : List (ℕ × R)) :
    toPoly (ofList l) = toPolyCore l := by
  unfold toPoly ofList ofSortedList
  dsimp only
  rw [toPolyCore_filter_nonzero, toPolyCore_dedupList, toPolyCore_mergeSort]

omit [DecidableEq R] in
lemma toPolyCore_mul_y (i : ℕ) (a : R) (y : List (ℕ × R)) :
    toPolyCore (y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) =
      (Polynomial.C a * Polynomial.X ^ i) * toPolyCore y := by
  induction y with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    rcases hd with ⟨j, b⟩
    change toPolyCore ([(i + j, a * b)] ++ tl.flatMap _) = _
    rw [toPolyCore_append, ih]
    dsimp only [toPolyCore]
    rw [show Polynomial.C (a * b) * Polynomial.X ^ (i + j) =
        Polynomial.C a * Polynomial.X ^ i * (Polynomial.C b * Polynomial.X ^ j) by
      rw [map_mul, pow_add]; ring]
    ring

omit [DecidableEq R] in
lemma toPolyCore_mul_x (x y : List (ℕ × R)) :
    toPolyCore (x.flatMap fun ⟨i, a⟩ => y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) =
    toPolyCore x * toPolyCore y := by
  induction x with
  | nil => simp [toPolyCore, List.flatMap]
  | cons hd tl ih =>
    rcases hd with ⟨i, a⟩
    change toPolyCore ((y.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) ++ tl.flatMap _) = _
    rw [toPolyCore_append, ih, toPolyCore_mul_y]
    dsimp only [toPolyCore]
    ring

theorem toPoly_one : toPoly (1 : SparsePoly R) = 1 := by
  change toPoly (C 1) = 1
  rw [toPoly_C]
  exact map_one (Polynomial.C (R := R))

theorem toPoly_mul (x y : SparsePoly R) : toPoly (x * y) = toPoly x * toPoly y := by
  rw [show x * y = ofList (x.coeffs.flatMap fun ⟨i, a⟩ =>
    y.coeffs.flatMap fun ⟨j, b⟩ => [(i + j, a * b)]) from rfl, toPoly_ofList]
  exact toPolyCore_mul_x x.coeffs y.coeffs

theorem toPoly_neg (x : SparsePoly R) : toPoly (-x) = -toPoly x := by
  change toPoly (C (-1) * x) = -toPoly x
  rw [toPoly_mul, toPoly_C]
  simp

instance : CommRing (SparsePoly R) where
  add := (·+·)
  zero := 0
  mul := (·*·)
  one := 1
  neg := (-·)
  sub x y := x + -y
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec
  natCast n := C (n : R)
  intCast z := C (z : R)

  add_assoc := by
    intro x y z
    apply toPoly_injective
    rw [toPoly_add, toPoly_add, toPoly_add, toPoly_add]
    exact add_assoc (toPoly x) (toPoly y) (toPoly z)
  zero_add := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_zero, zero_add]

  add_zero := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_zero, add_zero]

  add_comm := by
    intro a b
    apply toPoly_injective
    rw [toPoly_add, toPoly_add, add_comm]

  neg_add_cancel := by
    intro a
    apply toPoly_injective
    rw [toPoly_add, toPoly_neg, toPoly_zero, neg_add_cancel]

  mul_assoc := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_mul, toPoly_mul, toPoly_mul, mul_assoc]

  one_mul := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_one, one_mul]

  mul_one := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_one, mul_one]

  left_distrib := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul, left_distrib]

  right_distrib := by
    intro a b c
    apply toPoly_injective
    rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul, right_distrib]

  zero_mul := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_zero, zero_mul]

  mul_zero := by
    intro a
    apply toPoly_injective
    rw [toPoly_mul, toPoly_zero,  mul_zero]

  mul_comm := by
    intro a b
    apply toPoly_injective
    rw [toPoly_mul, toPoly_mul, mul_comm]

  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  natCast_zero := by
    apply toPoly_injective
    rw [toPoly_C, toPoly_zero]
    push_cast
    exact map_zero Polynomial.C

  natCast_succ := by
    intro n
    apply toPoly_injective
    show toPoly (C ((n + 1 : ℕ) : R)) = toPoly (C (n : R) + 1)
    rw [toPoly_C, toPoly_add, toPoly_C, toPoly_one]
    push_cast
    grind

  intCast_ofNat := by
    intro n
    apply toPoly_injective
    change toPoly (C ((Int.ofNat n : ℤ) : R)) = toPoly (C (n : R))
    rw [toPoly_C, toPoly_C]
    aesop

  intCast_negSucc := by
    intro n
    apply toPoly_injective
    change toPoly (C _) = toPoly (- C _)
    rw [toPoly_C, toPoly_neg, toPoly_C]
    push_cast
    grind

/-- The ring homomorphism `R →+* SparsePoly R` sending `r` to the constant polynomial `C r`. -/
def CHom : R →+* SparsePoly R where
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

instance : Algebra R (SparsePoly R) where
  smul := fun a r => C a * r
  algebraMap := CHom
  commutes' r p := mul_comm (C r) p
  smul_def' _ _ := rfl

end SparsePoly

/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.vector.zip
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Vector.Basic
import Mathbin.Data.List.Zip

/-!
# The `zip_with` operation on vectors.
-/


namespace Vector

section ZipWith

variable {α β γ : Type _} {n : ℕ} (f : α → β → γ)

/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
def zipWith : Vector α n → Vector β n → Vector γ n := fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩
#align vector.zip_with Vector.zipWith

@[simp]
theorem zip_with_to_list (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl
#align vector.zip_with_to_list Vector.zip_with_to_list

@[simp]
theorem zip_with_nth (x : Vector α n) (y : Vector β n) (i) :
    (Vector.zipWith f x y).nth i = f (x.nth i) (y.nth i) :=
  by
  dsimp only [Vector.zipWith, Vector.get]
  cases x; cases y
  simp only [List.nth_le_zip_with, Subtype.coe_mk]
  congr
#align vector.zip_with_nth Vector.zip_with_nth

@[simp]
theorem zip_with_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail :=
  by
  ext
  simp [nth_tail]
#align vector.zip_with_tail Vector.zip_with_tail

@[to_additive]
theorem prod_mul_prod_eq_prod_zip_with [CommMonoid α] (x y : Vector α n) :
    x.toList.Prod * y.toList.Prod = (Vector.zipWith (· * ·) x y).toList.Prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)
#align vector.prod_mul_prod_eq_prod_zip_with Vector.prod_mul_prod_eq_prod_zip_with
#align vector.sum_add_sum_eq_sum_zip_with Vector.sum_add_sum_eq_sum_zip_with

end ZipWith

end Vector


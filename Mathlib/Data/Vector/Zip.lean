/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Zip

#align_import data.vector.zip from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# The `zipWith` operation on vectors.
-/


namespace Vector

section ZipWith

variable {α β γ : Type*} {n : ℕ} (f : α → β → γ)

/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
def zipWith : Vector α n → Vector β n → Vector γ n := fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩
                                                                                             -- 🎉 no goals
#align vector.zip_with Vector.zipWith

@[simp]
theorem zipWith_toList (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl
#align vector.zip_with_to_list Vector.zipWith_toList

@[simp]
theorem zipWith_get (x : Vector α n) (y : Vector β n) (i) :
    (Vector.zipWith f x y).get i = f (x.get i) (y.get i) := by
  dsimp only [Vector.zipWith, Vector.get]
  -- ⊢ List.nthLe (List.zipWith f ↑x ↑y) ↑i (_ : ↑i < List.length (List.zipWith f ↑ …
  cases x; cases y
  -- ⊢ List.nthLe (List.zipWith f ↑{ val := val✝, property := property✝ } ↑y) ↑i (_ …
           -- ⊢ List.nthLe (List.zipWith f ↑{ val := val✝¹, property := property✝¹ } ↑{ val  …
  simp only [List.nthLe_zipWith]
  -- 🎉 no goals
#align vector.zip_with_nth Vector.zipWith_get

@[simp]
theorem zipWith_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail := by
  ext
  -- ⊢ get (tail (zipWith f x y)) m✝ = get (zipWith f (tail x) (tail y)) m✝
  simp [get_tail]
  -- 🎉 no goals
#align vector.zip_with_tail Vector.zipWith_tail

@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Vector α n) :
    x.toList.prod * y.toList.prod = (Vector.zipWith (· * ·) x y).toList.prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)
#align vector.prod_mul_prod_eq_prod_zip_with Vector.prod_mul_prod_eq_prod_zipWith
#align vector.sum_add_sum_eq_sum_zip_with Vector.sum_add_sum_eq_sum_zipWith

end ZipWith

end Vector

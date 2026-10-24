/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# Lemmas about `List.Vector.map₂`

`List.Vector.map₂ f x y` applies `f : α → β → γ` to each corresponding pair of elements of the
vectors `x` and `y`. This file used to define a second copy of this operation,
`List.Vector.zipWith`, which is now a deprecated alias of `List.Vector.map₂`.
-/

@[expose] public section

namespace List

namespace Vector

section Map₂

variable {α β γ : Type*} {n : ℕ} (f : α → β → γ)

@[deprecated (since := "2026-10-07")] alias zipWith := map₂

/-- `toList` turns `map₂ f` into `List.zipWith f`; `get_map₂` is the entrywise version. -/
@[simp]
theorem toList_map₂ (x : Vector α n) (y : Vector β n) :
    (map₂ f x y).toList = List.zipWith f x.toList y.toList :=
  rfl

@[deprecated (since := "2026-10-07")] alias zipWith_toList := toList_map₂

@[deprecated (since := "2026-10-07")] alias zipWith_get := get_map₂

/-- `tail` commutes with `map₂ f`. This is the vector version of `List.tail_zipWith`; unlike
`tail_map`, it holds for vectors of any length `n`, not just `n + 1`. -/
@[simp]
theorem tail_map₂ (x : Vector α n) (y : Vector β n) : (map₂ f x y).tail = map₂ f x.tail y.tail :=
  ext fun _ ↦ by simp [get_tail]

@[deprecated (since := "2026-10-07")] alias zipWith_tail := tail_map₂

/-- The product of the entries of `x` times the product of the entries of `y` is the product of
their entrywise products. This is the vector version of
`List.prod_mul_prod_eq_prod_zipWith_of_length_eq`, whose length hypothesis is automatic here. -/
@[to_additive /-- The sum of the entries of `x` plus the sum of the entries of `y` is the sum of
  their entrywise sums. This is the vector version of
  `List.sum_add_sum_eq_sum_zipWith_of_length_eq`, whose length hypothesis is automatic here. -/]
theorem prod_mul_prod_eq_prod_map₂ [CommMonoid α] (x y : Vector α n) :
    x.toList.prod * y.toList.prod = (map₂ (· * ·) x y).toList.prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq _ _ <| by simp

@[to_additive (attr := deprecated (since := "2026-10-07"))]
alias prod_mul_prod_eq_prod_zipWith := prod_mul_prod_eq_prod_map₂

end Map₂

end Vector

end List

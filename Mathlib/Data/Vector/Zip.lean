/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# Lemmas about `List.Vector.map₂`
-/

@[expose] public section

namespace List

namespace Vector

section Map₂

variable {α β γ : Type*} {n : ℕ} (f : α → β → γ)

@[deprecated (since := "2026-10-07")] alias zipWith := map₂

@[simp]
theorem toList_map₂ (x : Vector α n) (y : Vector β n) :
    (map₂ f x y).toList = List.zipWith f x.toList y.toList :=
  rfl

@[deprecated (since := "2026-10-07")] alias zipWith_toList := toList_map₂

@[deprecated (since := "2026-10-07")] alias zipWith_get := get_map₂

@[simp]
theorem tail_map₂ (x : Vector α n) (y : Vector β n) : (map₂ f x y).tail = map₂ f x.tail y.tail :=
  ext fun _ ↦ by simp [get_tail]

@[deprecated (since := "2026-10-07")] alias zipWith_tail := tail_map₂

@[to_additive]
theorem prod_mul_prod_eq_prod_map₂ [CommMonoid α] (x y : Vector α n) :
    x.toList.prod * y.toList.prod = (map₂ (· * ·) x y).toList.prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq _ _ <| by simp

@[to_additive (attr := deprecated (since := "2026-10-07"))]
alias prod_mul_prod_eq_prod_zipWith := prod_mul_prod_eq_prod_map₂

end Map₂

end Vector

end List

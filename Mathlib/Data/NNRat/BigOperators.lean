/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.NNRat.Defs

/-! # Casting lemmas for non-negative rational numbers involving sums and products
-/

public section

variable {α : Type*}

namespace NNRat

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] [CharZero K]

@[norm_cast]
theorem cast_listSum (l : List ℚ≥0) : (l.sum : K) = (l.map (↑)).sum :=
  map_list_sum (castHom _) _

@[norm_cast]
theorem cast_listProd (l : List ℚ≥0) : (l.prod : K) = (l.map (↑)).prod :=
  map_list_prod (castHom _) _

@[norm_cast]
theorem cast_multisetSum (s : Multiset ℚ≥0) : (s.sum : K) = (s.map (↑)).sum :=
  map_multiset_sum (castHom _) _

@[norm_cast]
theorem cast_sum (s : Finset α) (f : α → ℚ≥0) : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : K) :=
  map_sum (castHom _) _ _

end DivisionSemiring

section Semifield

variable {K : Type*} [Semifield K] [CharZero K]

@[norm_cast]
theorem cast_multisetProd (s : Multiset ℚ≥0) : (s.prod : K) = (s.map (↑)).prod :=
  map_multiset_prod (castHom _) _

@[norm_cast]
theorem cast_prod (s : Finset α) (f : α → ℚ≥0) : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : K) :=
  map_prod (castHom _) _ _

end Semifield

section Rat

theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a ∈ s, f a).toNNRat = ∑ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, cast_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a ∈ s, f a).toNNRat = ∏ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, cast_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

end Rat

end NNRat

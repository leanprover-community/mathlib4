/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.NNRat.Defs

/-! # Casting lemmas for non-negative rational numbers involving sums and products
-/

variable {α : Type*}

namespace NNRat

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.sum : ℚ) = (l.map (↑)).sum :=
  map_list_sum coeHom _

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.prod : ℚ) = (l.map (↑)).prod :=
  map_list_prod coeHom _

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.sum : ℚ) = (s.map (↑)).sum :=
  map_multiset_sum coeHom _

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.prod : ℚ) = (s.map (↑)).prod :=
  map_multiset_prod coeHom _

@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : ℚ) :=
  map_sum coeHom _ _

theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a ∈ s, f a).toNNRat = ∑ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, coe_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℚ) :=
  map_prod coeHom _ _

theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a ∈ s, f a).toNNRat = ∏ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, coe_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

end NNRat

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

section DivisionSemiring

variable {β : Type} [DivisionSemiring β] [CharZero β]

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.sum : β) = (l.map (↑)).sum :=
  map_list_sum (castHom _) _

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.prod : β) = (l.map (↑)).prod :=
  map_list_prod (castHom _) _

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.sum : β) = (s.map (↑)).sum :=
  map_multiset_sum (castHom _) _

@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : β) :=
  map_sum (castHom _) _ _

end DivisionSemiring

section Semifield

variable {β : Type} [Semifield β] [CharZero β]

@[norm_cast]
lemma coe_multiset_prod (s : Multiset ℚ≥0) : (s.prod : β) = (s.map (↑)).prod :=
  map_multiset_prod (castHom _) _

@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : β) :=
  map_prod (castHom _) _ _

end Semifield

section Rat

theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a ∈ s, f a).toNNRat = ∑ a ∈ s,(f a).toNNRat := by
  rw [← coe_inj, coe_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a ∈ s, f a).toNNRat = ∏ a ∈ s, (f a).toNNRat := by
  rw [← coe_inj, coe_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

end Rat

end NNRat

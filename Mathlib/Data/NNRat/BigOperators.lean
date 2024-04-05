/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.NNRat.Defs

/-! # Casting lemmas for non-negative rational numbers involving sums and products
-/

open BigOperators

variable {ι α : Type*}

namespace NNRat

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.sum : ℚ) = (l.map (↑)).sum :=
  coeHom.map_list_sum _
#align nnrat.coe_list_sum NNRat.coe_list_sum

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.prod : ℚ) = (l.map (↑)).prod :=
  coeHom.map_list_prod _
#align nnrat.coe_list_prod NNRat.coe_list_prod

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.sum : ℚ) = (s.map (↑)).sum :=
  coeHom.map_multiset_sum _
#align nnrat.coe_multiset_sum NNRat.coe_multiset_sum

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.prod : ℚ) = (s.map (↑)).prod :=
  coeHom.map_multiset_prod _
#align nnrat.coe_multiset_prod NNRat.coe_multiset_prod

@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
  coeHom.map_sum _ _
#align nnrat.coe_sum NNRat.coe_sum

theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a in s, f a).toNNRat = ∑ a in s, (f a).toNNRat := by
  rw [← coe_inj, coe_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]
#align nnrat.to_nnrat_sum_of_nonneg NNRat.toNNRat_sum_of_nonneg

@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
  coeHom.map_prod _ _
#align nnrat.coe_prod NNRat.coe_prod

theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a in s, f a).toNNRat = ∏ a in s, (f a).toNNRat := by
  rw [← coe_inj, coe_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]
#align nnrat.to_nnrat_prod_of_nonneg NNRat.toNNRat_prod_of_nonneg

end NNRat

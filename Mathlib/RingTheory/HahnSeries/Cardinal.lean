/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Cardinality of Hahn series

We define `HahnSeries.card` as the cardinality of the support of a Hahn series, and find bounds for
the cardinalities of different operations.

## Todo

- Bound the cardinality of the inverse.
- Build the subgroups, subrings, etc. of Hahn series with less than a given infinite cardinal.
-/

@[expose] public section

open Cardinal

namespace HahnSeries

variable {Γ R S : Type*} [PartialOrder Γ]

/-! ### Cardinality function -/

section Zero
variable [Zero R]

/-- The cardinality of the support of a Hahn series. -/
def card (x : HahnSeries Γ R) : Cardinal :=
  #x.support

theorem card_congr [Zero S] {x : HahnSeries Γ R} {y : HahnSeries Γ S} (h : x.support = y.support) :
    x.card = y.card := by
  simp_rw [card, h]

theorem card_mono [Zero S] {x : HahnSeries Γ R} {y : HahnSeries Γ S} (h : x.support ⊆ y.support) :
    x.card ≤ y.card :=
  mk_le_mk_of_subset h

@[simp]
theorem card_zero : card (0 : HahnSeries Γ R) = 0 := by
  simp [card]

theorem card_single_of_ne (a : Γ) {r : R} (h : r ≠ 0) : card (single a r) = 1 := by
  rw [card, support_single_of_ne h, mk_singleton]

theorem card_single_le (a : Γ) (r : R) : card (single a r) ≤ 1 :=
  (mk_le_mk_of_subset support_single_subset).trans_eq (mk_singleton a)

theorem card_map_le [Zero S] (x : HahnSeries Γ R) (f : ZeroHom R S) : (x.map f).card ≤ x.card :=
  card_mono <| support_map_subset ..

theorem card_truncLT_le [DecidableLT Γ] (x : HahnSeries Γ R) (c : Γ) :
    (truncLT c x).card ≤ x.card :=
  card_mono <| support_truncLT_subset ..

theorem card_smul_le (s : S) (x : HahnSeries Γ R) [SMulZeroClass S R] : (s • x).card ≤ x.card :=
  card_mono <| support_smul_subset ..

end Zero

theorem card_neg_le [NegZeroClass R] (x : HahnSeries Γ R) : (-x).card ≤ x.card :=
  card_mono <| support_neg_subset ..

theorem card_add_le [AddMonoid R] (x y : HahnSeries Γ R) : (x + y).card ≤ x.card + y.card :=
  (mk_le_mk_of_subset (support_add_subset ..)).trans (mk_union_le ..)

@[simp]
theorem card_neg [AddGroup R] (x : HahnSeries Γ R) : (-x).card = x.card :=
  card_congr support_neg

theorem card_sub_le [AddGroup R] (x y : HahnSeries Γ R) : (x - y).card ≤ x.card + y.card :=
  (mk_le_mk_of_subset (support_sub_subset ..)).trans (mk_union_le ..)

theorem card_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
    {x y : HahnSeries Γ R} : (x * y).card ≤ x.card * y.card :=
  (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le

end HahnSeries

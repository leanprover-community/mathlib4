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

We define `HahnSeries.cardSupp` as the cardinality of the support of a Hahn series, and find bounds
for the cardinalities of different operations.

## Todo

- Bound the cardinality of the inverse.
- Build the subgroups, subrings, etc. of Hahn series with support less than a given infinite
  cardinal.
-/

@[expose] public section

open Cardinal

namespace HahnSeries

variable {Γ R S : Type*} [PartialOrder Γ]

/-! ### Cardinality function -/

section Zero
variable [Zero R]

/-- The cardinality of the support of a Hahn series. -/
def cardSupp (x : R⟦Γ⟧) : Cardinal :=
  #x.support

theorem cardSupp_congr [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support) :
    x.cardSupp = y.cardSupp := by
  simp_rw [cardSupp, h]

theorem cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support ⊆ y.support) :
    x.cardSupp ≤ y.cardSupp :=
  mk_le_mk_of_subset h

@[simp]
theorem cardSupp_zero : cardSupp (0 : R⟦Γ⟧) = 0 := by
  simp [cardSupp]

theorem cardSupp_single_of_ne (a : Γ) {r : R} (h : r ≠ 0) : cardSupp (single a r) = 1 := by
  rw [cardSupp, support_single_of_ne h, mk_singleton]

theorem cardSupp_single_le (a : Γ) (r : R) : cardSupp (single a r) ≤ 1 :=
  (mk_le_mk_of_subset support_single_subset).trans_eq (mk_singleton a)

theorem cardSupp_map_le [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) : (x.map f).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_map_subset ..

theorem cardSupp_truncLT_le [DecidableLT Γ] (x : R⟦Γ⟧) (c : Γ) :
    (truncLT c x).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_truncLT_subset ..

theorem cardSupp_smul_le (s : S) (x : R⟦Γ⟧) [SMulZeroClass S R] : (s • x).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_smul_subset ..

end Zero

theorem cardSupp_neg_le [NegZeroClass R] (x : R⟦Γ⟧) : (-x).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_neg_subset ..

theorem cardSupp_add_le [AddMonoid R] (x y : R⟦Γ⟧) : (x + y).cardSupp ≤ x.cardSupp + y.cardSupp :=
  (mk_le_mk_of_subset (support_add_subset ..)).trans (mk_union_le ..)

@[simp]
theorem cardSupp_neg [AddGroup R] (x : R⟦Γ⟧) : (-x).cardSupp = x.cardSupp :=
  cardSupp_congr support_neg

theorem cardSupp_sub_le [AddGroup R] (x y : R⟦Γ⟧) : (x - y).cardSupp ≤ x.cardSupp + y.cardSupp :=
  (mk_le_mk_of_subset (support_sub_subset ..)).trans (mk_union_le ..)

theorem cardSupp_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
    (x y : R⟦Γ⟧) : (x * y).cardSupp ≤ x.cardSupp * y.cardSupp :=
  (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le

end HahnSeries

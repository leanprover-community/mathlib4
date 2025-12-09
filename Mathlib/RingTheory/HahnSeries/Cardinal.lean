/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.SetTheory.Cardinal.Arithmetic

import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Cardinality of Hahn series

We define `HahnSeries.card` as the cardinality of the support of a Hahn series, and find bounds for
the cardinalities of different operations. We also build the subgroups, subrings, etc. of Hahn
series bounded by a given infinite cardinal.
-/

@[expose] public section

open Cardinal

namespace HahnSeries

variable {Γ R S α : Type*}

/-! ### Cardinality function -/

section PartialOrder
variable [PartialOrder Γ]

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

@[simp]
theorem card_one_le [Zero Γ] [One R] : card (1 : HahnSeries Γ R) ≤ 1 :=
  card_single_le ..

@[simp]
theorem card_one [Zero Γ] [One R] [NeZero (1 : R)] : card (1 : HahnSeries Γ R) = 1 :=
  card_single_of_ne _ one_ne_zero

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
    (x y : HahnSeries Γ R) : (x * y).card ≤ x.card * y.card :=
  (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le

theorem card_single_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : HahnSeries Γ R) (a : Γ) (r : R) :
    (single a r * x).card ≤ x.card := by
  simpa using (card_mul_le ..).trans (mul_le_mul_left (card_single_le ..) _)

theorem card_mul_single_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : HahnSeries Γ R) (a : Γ) (r : R) :
    (x * single a r).card ≤ x.card := by
  simpa using (card_mul_le ..).trans (mul_le_mul_right (card_single_le ..) _)

theorem card_pow_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
    (x : HahnSeries Γ R) (n : ℕ) : (x ^ n).card ≤ x.card ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    simp_rw [pow_succ]
    exact (card_mul_le ..).trans <| mul_le_mul_left IH _

theorem card_hsum_le [AddCommMonoid R] (s : SummableFamily Γ R α) :
    lift s.hsum.card ≤ sum fun a : α ↦ (s a).card :=
  (lift_le.2 <| mk_le_mk_of_subset (SummableFamily.support_hsum_subset ..)).trans
    mk_iUnion_le_sum_mk_lift

end PartialOrder

section LinearOrder
variable [LinearOrder Γ]

theorem card_hsum_powers_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
    (x : HahnSeries Γ R) : (SummableFamily.powers x).hsum.card ≤ sum fun n ↦ x.card ^ n := by
  rw [← lift_uzero (card _)]
  refine (card_hsum_le _).trans <| sum_le_sum _ _ fun i ↦ ?_
  rw [SummableFamily.powers_toFun]
  split_ifs
  · exact card_pow_le ..
  · cases i <;> simp

theorem card_inv_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x : HahnSeries Γ R) :
    x⁻¹.card ≤ max ℵ₀ x.card := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  apply (sum_pow_le_max_aleph0 _).trans' <|
    (card_single_mul_le ..).trans <| (card_hsum_powers_le ..).trans _
  gcongr
  refine (card_single_mul_le _ (-x.order) x.leadingCoeff⁻¹).trans' <| card_mono fun _ ↦ ?_
  aesop (add simp [coeff_single_mul])

theorem card_div_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x y : HahnSeries Γ R) :
    (x / y).card ≤ x.card * max ℵ₀ y.card :=
  (card_mul_le ..).trans <| mul_le_mul_right (card_inv_le y) _

end LinearOrder

/-! ### Substructures -/

variable (c : Cardinal)

section AddMonoid
variable [PartialOrder Γ] [AddMonoid R] [hc : Fact (ℵ₀ ≤ c)]

variable (Γ R) in
/-- The submonoid of Hahn series with cardinal less than `c`. -/
@[simps!]
def cardLTAddSubmonoid : AddSubmonoid (HahnSeries Γ R) where
  carrier := {x | x.card < c}
  zero_mem' := by simpa using aleph0_pos.trans_le hc.out
  add_mem' hx hy := (card_add_le ..).trans_lt <| add_lt_of_lt hc.out hx hy

@[simp]
theorem mem_cardLTAddSubmonoid {x : HahnSeries Γ R} : x ∈ cardLTAddSubmonoid Γ R c ↔ x.card < c :=
  .rfl

end AddMonoid

section AddGroup
variable [PartialOrder Γ] [AddGroup R] [hc : Fact (ℵ₀ ≤ c)]

variable (Γ R) in
/-- The subgroup of Hahn series with cardinal less than `c`. -/
@[simps!]
def cardLTAddSubgroup : AddSubgroup (HahnSeries Γ R) where
  neg_mem' := by simp
  __ := cardLTAddSubmonoid Γ R c

@[simp]
theorem mem_cardLTAddSubgroup {x : HahnSeries Γ R} : x ∈ cardLTAddSubgroup Γ R c ↔ x.card < c :=
  .rfl

end AddGroup

section Subring
variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Ring R]
  [hc : Fact (ℵ₀ ≤ c)]

variable (Γ R) in
/-- The subring of Hahn series with cardinal less than `c`. -/
def cardLTSubring : Subring (HahnSeries Γ R) where
  one_mem' := card_one_le.trans_lt <| one_lt_aleph0.trans_le hc.out
  mul_mem' hx hy := (card_mul_le ..).trans_lt <| mul_lt_of_lt hc.out hx hy
  __ := cardLTAddSubgroup Γ R c

@[simp]
theorem mem_cardLTSubring {x : HahnSeries Γ R} : x ∈ cardLTSubring Γ R c ↔ x.card < c :=
  .rfl

end Subring

section Subfield
variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] [hc : Fact (ℵ₀ < c)]

variable (Γ R) in
/-- The subring of Hahn series with cardinal less than `c`. -/
@[simps!]
def cardLTSubfield : Subfield (HahnSeries Γ R) where
  inv_mem' _ _ := (card_inv_le _).trans_lt <| by simpa [Fact.out]
  __ := have : Fact (ℵ₀ ≤ c) := ⟨hc.out.le⟩; cardLTSubring Γ R c

@[simp]
theorem mem_cardLTSubfield {x : HahnSeries Γ R} : x ∈ cardLTSubfield Γ R c ↔ x.card < c :=
  .rfl

end Subfield
end HahnSeries

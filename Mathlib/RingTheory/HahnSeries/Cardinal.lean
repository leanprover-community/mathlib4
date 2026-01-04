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

We define `HahnSeries.cardSupp` as the cardinality of the support of a Hahn series, and find bounds
for the cardinalities of different operations. We also build the subgroups, subrings, etc. of Hahn
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

@[simp]
theorem cardSupp_one_le [Zero Γ] [One R] : cardSupp (1 : R⟦Γ⟧) ≤ 1 :=
  cardSupp_single_le ..

@[simp]
theorem cardSupp_one [Zero Γ] [One R] [NeZero (1 : R)] : cardSupp (1 : R⟦Γ⟧) = 1 :=
  cardSupp_single_of_ne _ one_ne_zero

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

theorem cardSupp_single_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) :
    (single a r * x).cardSupp ≤ x.cardSupp := by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_left (cardSupp_single_le ..) _)

theorem cardSupp_mul_single_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) :
    (x * single a r).cardSupp ≤ x.cardSupp := by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_right (cardSupp_single_le ..) _)

theorem cardSupp_pow_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
    (x : R⟦Γ⟧) (n : ℕ) : (x ^ n).cardSupp ≤ x.cardSupp ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    simpa [pow_succ] using (cardSupp_mul_le ..).trans <| mul_le_mul_left IH _

theorem cardSupp_hsum_le [AddCommMonoid R] (s : SummableFamily Γ R α) :
    lift s.hsum.cardSupp ≤ sum fun a ↦ (s a).cardSupp :=
  (lift_le.2 <| mk_le_mk_of_subset (SummableFamily.support_hsum_subset ..)).trans
    mk_iUnion_le_sum_mk_lift

end PartialOrder

section LinearOrder
variable [LinearOrder Γ]

theorem cardSupp_hsum_powers_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
    (x : R⟦Γ⟧) : (SummableFamily.powers x).hsum.cardSupp ≤ max ℵ₀ x.cardSupp := by
  grw [← lift_uzero (cardSupp _), ← sum_pow_le_max_aleph0, cardSupp_hsum_le, sum_le_sum]
  intro i
  rw [SummableFamily.powers_toFun]
  split_ifs
  · exact cardSupp_pow_le ..
  · cases i <;> simp

theorem cardSupp_inv_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x : R⟦Γ⟧) :
    x⁻¹.cardSupp ≤ max ℵ₀ x.cardSupp := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  apply (cardSupp_single_mul_le ..).trans <| (cardSupp_hsum_powers_le ..).trans _
  gcongr
  refine (cardSupp_single_mul_le _ (-x.order) x.leadingCoeff⁻¹).trans' <| cardSupp_mono fun _ ↦ ?_
  aesop (add simp [coeff_single_mul])

theorem cardSupp_div_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x y : R⟦Γ⟧) :
    (x / y).cardSupp ≤ x.cardSupp * max ℵ₀ y.cardSupp :=
  (cardSupp_mul_le ..).trans <| mul_le_mul_right (cardSupp_inv_le y) _

end LinearOrder

/-! ### Substructures -/

variable (κ : Cardinal)

section AddMonoid
variable [PartialOrder Γ] [AddMonoid R] [hκ : Fact (ℵ₀ ≤ κ)]

variable (Γ R) in
/-- The `κ`-bounded submonoid of Hahn series with less than `κ` terms. -/
@[simps!]
def cardSuppLTAddSubmonoid : AddSubmonoid R⟦Γ⟧ where
  carrier := {x | x.cardSupp < κ}
  zero_mem' := by simpa using aleph0_pos.trans_le hκ.out
  add_mem' hx hy := (cardSupp_add_le ..).trans_lt <| add_lt_of_lt hκ.out hx hy

@[simp]
theorem mem_cardSuppLTAddSubmonoid {x : R⟦Γ⟧} : x ∈ cardSuppLTAddSubmonoid Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end AddMonoid

section AddGroup
variable [PartialOrder Γ] [AddGroup R] [hκ : Fact (ℵ₀ ≤ κ)]

variable (Γ R) in
/-- The `κ`-bounded subgroup of Hahn series with less than `κ` terms. -/
@[simps!]
def cardSuppLTAddSubgroup : AddSubgroup R⟦Γ⟧ where
  neg_mem' := by simp
  __ := cardSuppLTAddSubmonoid Γ R κ

@[simp]
theorem mem_cardSuppLTAddSubgroup {x : R⟦Γ⟧} : x ∈ cardSuppLTAddSubgroup Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end AddGroup

section Subring
variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Ring R]
  [hκ : Fact (ℵ₀ ≤ κ)]

variable (Γ R) in
/-- The `κ`-bounded subring of Hahn series with less than `κ` terms. -/
def cardSuppLTSubring : Subring R⟦Γ⟧ where
  one_mem' := cardSupp_one_le.trans_lt <| one_lt_aleph0.trans_le hκ.out
  mul_mem' hx hy := (cardSupp_mul_le ..).trans_lt <| mul_lt_of_lt hκ.out hx hy
  __ := cardSuppLTAddSubgroup Γ R κ

@[simp]
theorem mem_cardSuppLTSubring {x : R⟦Γ⟧} : x ∈ cardSuppLTSubring Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end Subring

section Subfield
variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] [hκ : Fact (ℵ₀ < κ)]

variable (Γ R) in
/-- The `κ`-bounded subfield of Hahn series with less than `κ` terms. -/
@[simps!]
def cardSuppLTSubfield : Subfield R⟦Γ⟧ where
  inv_mem' _ _ := (cardSupp_inv_le _).trans_lt <| by simpa [hκ.out]
  __ := have : Fact (ℵ₀ ≤ κ) := ⟨hκ.out.le⟩; cardSuppLTSubring Γ R κ

@[simp]
theorem mem_cardSuppLTSubfield {x : R⟦Γ⟧} : x ∈ cardSuppLTSubfield Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end Subfield
end HahnSeries

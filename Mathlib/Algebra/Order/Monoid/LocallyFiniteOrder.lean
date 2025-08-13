/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Embedding
import Mathlib.Order.Interval.Finset.Basic

/-!

# Locally Finite Linearly Ordered Abelian Groups

## Main results
- `LocallyFiniteOrder.orderAddMonoidEquiv`:
  Any nontrivial linearly ordered additive abelian group that is locally finite is
  isomorphic to `ℤ`.
- `LocallyFiniteOrder.orderMonoidEquiv`:
  Any nontrivial linearly ordered abelian group that is locally finite is isomorphic to
  `Multiplicative ℤ`.
- `LocallyFiniteOrder.orderMonoidWithZeroEquiv`:
  Any nontrivial linearly ordered abelian group with zero that is locally finite
  is isomorphic to `ℤᵐ⁰`.

-/

open Finset

section Multiplicative

variable {M : Type*} [CancelCommMonoid M] [LinearOrder M] [IsOrderedMonoid M] [LocallyFiniteOrder M]

@[to_additive]
lemma Finset.card_Ico_mul_right [ExistsMulOfLE M] (a b c : M) :
    #(Ico (a * c) (b * c)) = #(Ico a b) := by
  have : (Ico (a * c) (b * c)) = (Ico a b).map (mulRightEmbedding c) := by
    ext x
    simp only [mem_Ico, mem_map, mulRightEmbedding_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨d, rfl⟩ := exists_mul_of_le h₁
      exact ⟨a * d, ⟨by simpa using h₁, by simpa [mul_right_comm a c d] using h₂⟩,
        by simp_rw [mul_assoc, mul_comm]⟩
    · aesop
  simp [this]

@[to_additive]
lemma card_Ico_one_mul [ExistsMulOfLE M] (a b : M)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    #(Ico 1 (a * b)) = #(Ico 1 a) + #(Ico 1 b) := by
  have : Ico 1 b ∪ Ico (1 * b) (a * b) = Ico 1 (a * b) := by
    simp [Ico_union_Ico, ha, hb, Right.one_le_mul ha hb]
  rw [← this, Finset.card_union, Finset.card_Ico_mul_right]
  simp [add_comm]

end Multiplicative

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

variable (G) in
/-- The canonical embedding (as a monoid hom) from a linearly ordered cancellative additive monoid
into `ℤ`. This is either surjective or zero. -/
def LocallyFiniteOrder.addMonoidHom :
    G →+ ℤ where
  toFun a := #(Ico 0 a) - #(Ico 0 (-a))
  map_zero' := by simp
  map_add' a b := by
    wlog hab : a ≤ b generalizing a b
    · convert this b a (le_of_not_ge hab) using 1 <;> simp only [add_comm]
    obtain ha | ha := le_total 0 a <;> obtain hb | hb := le_total 0 b
    · have : -b ≤ a := by trans 0 <;> simp [ha, hb]
      simp [ha, hb, card_Ico_zero_add, this]
    · obtain rfl := hb.antisymm (ha.trans hab)
      obtain rfl := ha.antisymm hab
      simp
    · simp only [neg_add_rev, ha, Ico_eq_empty_of_le, card_empty, Nat.cast_zero, zero_sub,
        Left.neg_nonpos_iff, hb, sub_zero]
      obtain ⟨b, rfl⟩ : ∃ r, b = r - a := ⟨a + b, by abel⟩
      simp only [add_sub_cancel, neg_sub, sub_add_eq_add_sub, add_neg_cancel, zero_sub]
      obtain hb' | hb' := le_total 0 b
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, ← Nat.cast_add,
          ← card_Ico_zero_add, ha, ← sub_eq_add_neg]
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, sub_eq_iff_eq_add,
          ← Nat.cast_add, ← card_Ico_zero_add, hb, sub_add_eq_add_sub]
    · have : ¬0 < a + b := by simpa using add_nonpos ha hb
      simp [ha, hb, card_Ico_zero_add, Ico_eq_empty, this]

variable (G) in
/-- The canonical embedding (as an ordered monoid hom) from a linearly ordered cancellative
group into `ℤ`. This is either surjective or zero. -/
def LocallyFiniteOrder.orderAddMonoidHom :
    G →+o ℤ where
  __ := addMonoidHom G
  monotone' a b hab := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    replace hab : 0 ≤ b := by simpa using hab
    suffices 0 ≤ addMonoidHom G b by simpa
    simp [addMonoidHom, hab]

@[simp]
lemma LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom :
    orderAddMonoidHom G = addMonoidHom G := rfl

@[simp]
lemma LocallyFiniteOrder.orderAddMonoidHom_apply (x : G) :
    orderAddMonoidHom G x = addMonoidHom G x := rfl

lemma LocallyFiniteOrder.orderAddMonoidHom_strictMono :
    StrictMono (orderAddMonoidHom G) := by
  rw [strictMono_iff_map_pos]
  intro g H
  simpa [addMonoidHom, H.le]

lemma LocallyFiniteOrder.orderAddMonoidHom_bijective [Nontrivial G] :
    Function.Bijective (orderAddMonoidHom G) := by
  refine ⟨orderAddMonoidHom_strictMono.injective, ?_⟩
  suffices 1 ∈ (orderAddMonoidHom G).range by
    obtain ⟨x, hx⟩ := this
    exact fun a ↦ ⟨a • x, by simp_all⟩
  have ⟨a, ha⟩ := exists_zero_lt (α := G)
  obtain ⟨b, hb⟩ := exists_covBy_of_wellFoundedLT (α := Icc 0 a) (a := ⟨0, by simpa using ha.le⟩)
    (fun H ↦ ha.not_ge (@H ⟨a, by simpa using ha.le⟩ ha.le))
  use b.1
  have : 0 ≤ b.1 := hb.1.le
  suffices Ico 0 b.1 = {0} by simpa [orderAddMonoidHom, addMonoidHom, this]
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hx'
    have := b.2
    simp only [Finset.mem_Icc] at this
    exact hb.2 (c := ⟨x, by simpa [h₁] using h₂.le.trans this.2⟩)
      (lt_of_le_of_ne h₁ (by simpa using Ne.symm hx')) h₂
  · rintro rfl
    simpa using hb.1

variable (G) in
/-- Any nontrivial linearly ordered abelian group that is locally finite is isomorphic to `ℤ`. -/
noncomputable
def LocallyFiniteOrder.orderAddMonoidEquiv [Nontrivial G] :
    G ≃+o ℤ where
  __ := orderAddMonoidHom G
  __ := AddEquiv.ofBijective (orderAddMonoidHom G) orderAddMonoidHom_bijective
  map_le_map_iff' {a b} := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    suffices 0 ≤ orderAddMonoidHom G b ↔ 0 ≤ b by simpa
    obtain hb | hb := le_total 0 b
    · simp [orderAddMonoidHom, addMonoidHom, hb]
    · simp [orderAddMonoidHom, addMonoidHom, hb]

lemma LocallyFiniteOrder.orderAddMonoidEquiv_apply [Nontrivial G] (x : G) :
    orderAddMonoidEquiv G x = addMonoidHom G x := rfl

/-- Any linearly ordered abelian group that is locally finite embeds to `Multiplicative ℤ`. -/
noncomputable
def LocallyFiniteOrder.orderMonoidEquiv (G : Type*) [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] [Nontrivial G] :
    G ≃*o Multiplicative ℤ :=
  have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  (orderAddMonoidEquiv (Additive G)).toMultiplicative

/-- Any linearly ordered abelian group that is locally finite embeds into `Multiplicative ℤ`. -/
noncomputable
def LocallyFiniteOrder.orderMonoidHom (G : Type*) [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    G →*o Multiplicative ℤ :=
  have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  ⟨(orderAddMonoidHom (Additive G)).toMultiplicative, (orderAddMonoidHom (Additive G)).2⟩

lemma LocallyFiniteOrder.orderMonoidHom_strictMono {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    StrictMono (orderMonoidHom G) :=
  let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  fun a b h ↦ orderAddMonoidHom_strictMono h

open scoped WithZero in
/-- Any nontrivial linearly ordered abelian group with zero that is locally finite
is isomorphic to `ℤᵐ⁰`. -/
noncomputable
def LocallyFiniteOrder.orderMonoidWithZeroEquiv (G : Type*) [LinearOrderedCommGroupWithZero G]
    [LocallyFiniteOrder Gˣ] [Nontrivial Gˣ] : G ≃*o ℤᵐ⁰ :=
  OrderMonoidIso.withZeroUnits.symm.trans (LocallyFiniteOrder.orderMonoidEquiv _).withZero

open scoped WithZero in
/-- Any linearly ordered abelian group with zero that is locally finite embeds into `ℤᵐ⁰`. -/
noncomputable
def LocallyFiniteOrder.orderMonoidWithZeroHom (G : Type*) [LinearOrderedCommGroupWithZero G]
    [LocallyFiniteOrder Gˣ] : G →*₀o ℤᵐ⁰ where
  __ := (WithZero.map' (orderMonoidHom Gˣ)).comp
    OrderMonoidIso.withZeroUnits.symm.toMonoidWithZeroHom
  monotone' a b h := by have := (orderMonoidHom Gˣ).monotone'; aesop

lemma LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono {G : Type*}
    [LinearOrderedCommGroupWithZero G] [LocallyFiniteOrder Gˣ] :
    StrictMono (orderMonoidWithZeroHom G) := by
  have := orderMonoidHom_strictMono (G := Gˣ)
  intro a b h
  aesop (add simp orderMonoidWithZeroHom)

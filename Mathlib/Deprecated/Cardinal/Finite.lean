/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Deprecated.Cardinal.PartENat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Card

/-!
# Deprecated material on `PartENat.card`.
-/

noncomputable section

universe u v
variable {α : Type u}

open Cardinal

namespace PartENat

/-- `PartENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `PartENat.card α = ⊤`. -/
@[deprecated ENat.card (since := "2024-12-01")]
def card (α : Type*) : PartENat :=
  toPartENat (mk α)

-- This rest of this file is about the deprecated `PartENat.card`.
set_option linter.deprecated false

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_toPartENat_eq_coe_card

@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_toPartENat_of_infinite

@[simp]
theorem card_sum (α β : Type*) :
    PartENat.card (α ⊕ β) = PartENat.card α + PartENat.card β := by
  simp only [PartENat.card, Cardinal.mk_sum, map_add, Cardinal.toPartENat_lift]

theorem card_congr {α : Type*} {β : Type*} (f : α ≃ β) : PartENat.card α = PartENat.card β :=
  Cardinal.toPartENat_congr f

@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

theorem card_image_of_injOn {α : Type u} {β : Type v} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem card_image_of_injective {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

-- Should I keep the 6 following lemmas ?
-- TODO: Add ofNat, zero, and one versions for simp confluence
@[simp]
theorem _root_.Cardinal.natCast_le_toPartENat_iff {n : ℕ} {c : Cardinal} :
    ↑n ≤ toPartENat c ↔ ↑n ≤ c := by
  rw [← toPartENat_natCast n, toPartENat_le_iff_of_le_aleph0 (le_of_lt (nat_lt_aleph0 n))]

@[simp]
theorem _root_.Cardinal.toPartENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
    toPartENat c ≤ n ↔ c ≤ n := by
  rw [← toPartENat_natCast n, toPartENat_le_iff_of_lt_aleph0 (nat_lt_aleph0 n)]

@[simp]
theorem _root_.Cardinal.natCast_eq_toPartENat_iff {n : ℕ} {c : Cardinal} :
    ↑n = toPartENat c ↔ ↑n = c := by
  rw [le_antisymm_iff, le_antisymm_iff, Cardinal.toPartENat_le_natCast_iff,
    Cardinal.natCast_le_toPartENat_iff]

@[simp]
theorem _root_.Cardinal.toPartENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
    Cardinal.toPartENat c = n ↔ c = n := by
  rw [eq_comm, Cardinal.natCast_eq_toPartENat_iff, eq_comm]

@[simp]
theorem _root_.Cardinal.natCast_lt_toPartENat_iff {n : ℕ} {c : Cardinal} :
    ↑n < toPartENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toPartENat_le_natCast_iff]

@[simp]
theorem _root_.Cardinal.toPartENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
    toPartENat c < ↑n ↔ c < ↑n := by
  simp only [← not_le, Cardinal.natCast_le_toPartENat_iff]

theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  rw [← Cardinal.mk_eq_zero_iff]
  conv_rhs => rw [← Nat.cast_zero]
  simp only [← Cardinal.toPartENat_eq_natCast_iff]
  simp only [PartENat.card, Nat.cast_zero]

theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  rw [← le_one_iff_subsingleton]
  conv_rhs => rw [← Nat.cast_one]
  rw [← Cardinal.toPartENat_le_natCast_iff]
  simp only [PartENat.card, Nat.cast_one]

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toPartENat_iff]
  simp only [PartENat.card, Nat.cast_one]

set_option linter.deprecated false in
@[deprecated ENat.card_eq_coe_natCard (since := "2024-11-30")]
theorem card_eq_coe_natCard (α : Type*) [Finite α] : card α = Nat.card α := by
  unfold PartENat.card
  apply symm
  rw [Cardinal.natCast_eq_toPartENat_iff]
  exact Nat.cast_card


end PartENat

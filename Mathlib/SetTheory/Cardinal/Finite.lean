/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.ULift
import Mathlib.Data.ZMod.Defs
import Mathlib.SetTheory.Cardinal.Basic

#align_import set_theory.cardinal.finite from "leanprover-community/mathlib"@"3ff3f2d6a3118b8711063de7111a0d77a53219a8"

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `PartENat.card α` is the cardinality of `α` as an extended natural number
  (using `Part ℕ`). If `α` is infinite, `PartENat.card α = ⊤`.
-/

set_option autoImplicit true

open Cardinal Function
open scoped BigOperators

noncomputable section

variable {α β : Type*}

namespace Nat

/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
#align nat.card Nat.card

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card
#align nat.card_eq_fintype_card Nat.card_eq_fintype_card

lemma card_eq_zero_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp [Nat.card]
@[simp] lemma card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 := mk_toNat_of_infinite
#align nat.card_eq_zero_of_infinite Nat.card_eq_zero_of_infinite

lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]

lemma card_ne_zero : Nat.card α ≠ 0 ↔ Nonempty α ∧ Finite α := by simp [card_eq_zero, not_or]

lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]

@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α := (card_ne_zero.1 h).2
#align nat.finite_of_card_ne_zero Nat.finite_of_card_ne_zero

theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f
#align nat.card_congr Nat.card_congr

lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α → β)
    (hf : Injective f) : Nat.card α ≤ Nat.card β := by
  simpa using toNat_le_of_le_of_lt_aleph0 (by simp [lt_aleph0_of_finite]) $
    mk_le_of_injective (α := ULift.{max u v} α) (β := ULift.{max u v} β) $ ULift.map_injective.2 hf

lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α → β)
    (hf : Surjective f) : Nat.card β ≤ Nat.card α := by
  simpa using toNat_le_of_le_of_lt_aleph0 (by simp [lt_aleph0_of_finite]) $ mk_le_of_surjective
    (α := ULift.{max u v} α) (β := ULift.{max u v} β) $ ULift.map_surjective.2 hf

theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)
#align nat.card_eq_of_bijective Nat.card_eq_of_bijective

theorem card_eq_of_equiv_fin {α : Type*} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f
#align nat.card_eq_of_equiv_fin Nat.card_eq_of_equiv_fin

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `Fin (Nat.card α)`. See also `Finite.equivFin`. -/
def equivFinOfCardPos {α : Type*} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq] at h
#align nat.equiv_fin_of_card_pos Nat.equivFinOfCardPos

theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]
#align nat.card_of_subsingleton Nat.card_of_subsingleton

-- @[simp] -- Porting note: simp can prove this
theorem card_unique [Unique α] : Nat.card α = 1 :=
  card_of_subsingleton default
#align nat.card_unique Nat.card_unique

theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique
#align nat.card_eq_one_iff_unique Nat.card_eq_one_iff_unique

theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α :=
  toNat_eq_ofNat.trans mk_eq_two_iff
#align nat.card_eq_two_iff Nat.card_eq_two_iff

theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  toNat_eq_ofNat.trans (mk_eq_two_iff' x)
#align nat.card_eq_two_iff' Nat.card_eq_two_iff'

theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp
#align nat.card_of_is_empty Nat.card_of_isEmpty

@[simp]
theorem card_sum [Finite α] [Finite β] : Nat.card (α ⊕ β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, toNat_mul, toNat_lift]
#align nat.card_prod Nat.card_prod

@[simp]
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift
#align nat.card_ulift Nat.card_ulift

@[simp]
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift
#align nat.card_plift Nat.card_plift

theorem card_pi {β : α → Type*} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, toNat_lift, toNat_finset_prod]
#align nat.card_pi Nat.card_pi

theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α := by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
#align nat.card_fun Nat.card_fun

@[simp]
theorem card_zmod (n : ℕ) : Nat.card (ZMod n) = n := by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]
#align nat.card_zmod Nat.card_zmod

end Nat

namespace PartENat

/-- `PartENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `PartENat.card α = ⊤`. -/
def card (α : Type*) : PartENat :=
  toPartENat (mk α)
#align part_enat.card PartENat.card

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_toPartENat_eq_coe_card
#align part_enat.card_eq_coe_fintype_card PartENat.card_eq_coe_fintype_card

@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_toPartENat_of_infinite
#align part_enat.card_eq_top_of_infinite PartENat.card_eq_top_of_infinite

@[simp]
theorem card_sum (α β : Type*) :
    PartENat.card (α ⊕ β) = PartENat.card α + PartENat.card β := by
  simp only [PartENat.card, Cardinal.mk_sum, map_add, Cardinal.toPartENat_lift]

theorem card_congr {α : Type*} {β : Type*} (f : α ≃ β) : PartENat.card α = PartENat.card β :=
  Cardinal.toPartENat_congr f
#align part_enat.card_congr PartENat.card_congr

theorem card_uLift (α : Type*) : card (ULift α) = card α :=
  card_congr Equiv.ulift
#align part_enat.card_ulift PartENat.card_uLift

@[simp]
theorem card_pLift (α : Type*) : card (PLift α) = card α :=
  card_congr Equiv.plift
#align part_enat.card_plift PartENat.card_pLift

lemma card_mono {s t : Set α} (ht : t.Finite) (h : s ⊆ t) : Nat.card s ≤ Nat.card t :=
  toNat_le_of_le_of_lt_aleph0 ht.lt_aleph0 <| mk_le_mk_of_subset h

theorem card_image_of_injOn {α : Type u} {β : Type v} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm
#align part_enat.card_image_of_inj_on PartENat.card_image_of_injOn

theorem card_image_of_injective {α : Type u} {β : Type v} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s :=
  card_image_of_injOn (Set.injOn_of_injective h s)
#align part_enat.card_image_of_injective PartENat.card_image_of_injective

-- Should I keeep the 6 following lemmas ?
@[simp]
theorem _root_.Cardinal.natCast_le_toPartENat_iff {n : ℕ} {c : Cardinal} :
    ↑n ≤ toPartENat c ↔ ↑n ≤ c := by
  rw [← toPartENat_cast n, toPartENat_le_iff_of_le_aleph0 (le_of_lt (nat_lt_aleph0 n))]
#align cardinal.coe_nat_le_to_part_enat_iff Cardinal.natCast_le_toPartENat_iff

@[simp]
theorem _root_.Cardinal.toPartENat_le_natCast_iff {c : Cardinal} {n : ℕ} :
    toPartENat c ≤ n ↔ c ≤ n := by
  rw [← toPartENat_cast n, toPartENat_le_iff_of_lt_aleph0 (nat_lt_aleph0 n)]
#align cardinal.to_part_enat_le_coe_nat_iff Cardinal.toPartENat_le_natCast_iff

@[simp]
theorem _root_.Cardinal.natCast_eq_toPartENat_iff {n : ℕ} {c : Cardinal} :
    ↑n = toPartENat c ↔ ↑n = c := by
  rw [le_antisymm_iff, le_antisymm_iff, Cardinal.toPartENat_le_natCast_iff,
    Cardinal.natCast_le_toPartENat_iff]
#align cardinal.coe_nat_eq_to_part_enat_iff Cardinal.natCast_eq_toPartENat_iff

@[simp]
theorem _root_.Cardinal.toPartENat_eq_natCast_iff {c : Cardinal} {n : ℕ} :
    Cardinal.toPartENat c = n ↔ c = n := by
rw [eq_comm, Cardinal.natCast_eq_toPartENat_iff, eq_comm]
#align cardinal.to_part_nat_eq_coe_nat_iff_eq Cardinal.toPartENat_eq_natCast_iff

@[simp]
theorem _root_.Cardinal.natCast_lt_toPartENat_iff {n : ℕ} {c : Cardinal} :
    ↑n < toPartENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toPartENat_le_natCast_iff]
#align part_enat.coe_nat_lt_coe_iff_lt Cardinal.natCast_lt_toPartENat_iff

@[simp]
theorem _root_.Cardinal.toPartENat_lt_natCast_iff {n : ℕ} {c : Cardinal} :
    toPartENat c < ↑n ↔ c < ↑n :=
by simp only [← not_le, Cardinal.natCast_le_toPartENat_iff]
#align lt_coe_nat_iff_lt Cardinal.toPartENat_lt_natCast_iff

theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  rw [← Cardinal.mk_eq_zero_iff]
  conv_rhs => rw [← Nat.cast_zero]
  simp only [← Cardinal.toPartENat_eq_natCast_iff]
  simp only [PartENat.card, Nat.cast_zero]
#align part_enat.card_eq_zero_iff_empty PartENat.card_eq_zero_iff_empty

theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  rw [← le_one_iff_subsingleton]
  conv_rhs => rw [← Nat.cast_one]
  rw [← Cardinal.toPartENat_le_natCast_iff]
  simp only [PartENat.card, Nat.cast_one]
#align part_enat.card_le_one_iff_subsingleton PartENat.card_le_one_iff_subsingleton

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toPartENat_iff]
  simp only [PartENat.card, Nat.cast_one]
#align part_enat.one_lt_card_iff_nontrivial PartENat.one_lt_card_iff_nontrivial

end PartENat

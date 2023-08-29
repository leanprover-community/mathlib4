/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.SetTheory.Cardinal.Finite

#align_import data.finite.card from "leanprover-community/mathlib"@"3ff3f2d6a3118b8711063de7111a0d77a53219a8"

/-!

# Cardinality of finite types

The cardinality of a finite type `α` is given by `Nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `Finite` instance
for the type. (Note: we could have defined a `Finite.card` that required you to
supply a `Finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `Nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `SetTheory.Cardinal.Finite` module.

-/


noncomputable section

open Classical

variable {α β γ : Type*}

/-- There is (noncomputably) an equivalence between a finite type `α` and `Fin (Nat.card α)`. -/
def Finite.equivFin (α : Type*) [Finite α] : α ≃ Fin (Nat.card α) := by
  have := (Finite.exists_equiv_fin α).choose_spec.some
  -- ⊢ α ≃ Fin (Nat.card α)
  rwa [Nat.card_eq_of_equiv_fin this]
  -- 🎉 no goals
#align finite.equiv_fin Finite.equivFin

/-- Similar to `Finite.equivFin` but with control over the term used for the cardinality. -/
def Finite.equivFinOfCardEq [Finite α] {n : ℕ} (h : Nat.card α = n) : α ≃ Fin n := by
  subst h
  -- ⊢ α ≃ Fin (Nat.card α)
  apply Finite.equivFin
  -- 🎉 no goals
#align finite.equiv_fin_of_card_eq Finite.equivFinOfCardEq

theorem Nat.card_eq (α : Type*) :
    Nat.card α = if h : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  -- ⊢ Nat.card α = if h : Finite α then Fintype.card α else 0
  · letI := Fintype.ofFinite α
    -- ⊢ Nat.card α = if h : Finite α then Fintype.card α else 0
    simp only [*, Nat.card_eq_fintype_card, dif_pos]
    -- 🎉 no goals
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]
    -- 🎉 no goals
#align nat.card_eq Nat.card_eq

theorem Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  haveI := Fintype.ofFinite α
  -- ⊢ 0 < Nat.card α ↔ Nonempty α
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff]
  -- 🎉 no goals
#align finite.card_pos_iff Finite.card_pos_iff

theorem Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.card α :=
  Finite.card_pos_iff.mpr h
#align finite.card_pos Finite.card_pos

namespace Finite

theorem cast_card_eq_mk {α : Type*} [Finite α] : ↑(Nat.card α) = Cardinal.mk α :=
  Cardinal.cast_toNat_of_lt_aleph0 (Cardinal.lt_aleph0_of_finite α)
#align finite.cast_card_eq_mk Finite.cast_card_eq_mk

theorem card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card α = Nat.card β ↔ Nonempty (α ≃ β)
  haveI := Fintype.ofFinite β
  -- ⊢ Nat.card α = Nat.card β ↔ Nonempty (α ≃ β)
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq]
  -- 🎉 no goals
#align finite.card_eq Finite.card_eq

theorem card_le_one_iff_subsingleton [Finite α] : Nat.card α ≤ 1 ↔ Subsingleton α := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card α ≤ 1 ↔ Subsingleton α
  simp only [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]
  -- 🎉 no goals
#align finite.card_le_one_iff_subsingleton Finite.card_le_one_iff_subsingleton

theorem one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α := by
  haveI := Fintype.ofFinite α
  -- ⊢ 1 < Nat.card α ↔ Nontrivial α
  simp only [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff_nontrivial]
  -- 🎉 no goals
#align finite.one_lt_card_iff_nontrivial Finite.one_lt_card_iff_nontrivial

theorem one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.card α :=
  one_lt_card_iff_nontrivial.mpr h
#align finite.one_lt_card Finite.one_lt_card

@[simp]
theorem card_option [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card (Option α) = Nat.card α + 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  -- 🎉 no goals
#align finite.card_option Finite.card_option

theorem card_le_of_injective [Finite β] (f : α → β) (hf : Function.Injective f) :
    Nat.card α ≤ Nat.card β := by
  haveI := Fintype.ofFinite β
  -- ⊢ Nat.card α ≤ Nat.card β
  haveI := Fintype.ofInjective f hf
  -- ⊢ Nat.card α ≤ Nat.card β
  simpa only [Nat.card_eq_fintype_card, ge_iff_le] using Fintype.card_le_of_injective f hf
  -- 🎉 no goals
#align finite.card_le_of_injective Finite.card_le_of_injective

theorem card_le_of_embedding [Finite β] (f : α ↪ β) : Nat.card α ≤ Nat.card β :=
  card_le_of_injective _ f.injective
#align finite.card_le_of_embedding Finite.card_le_of_embedding

theorem card_le_of_surjective [Finite α] (f : α → β) (hf : Function.Surjective f) :
    Nat.card β ≤ Nat.card α := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card β ≤ Nat.card α
  haveI := Fintype.ofSurjective f hf
  -- ⊢ Nat.card β ≤ Nat.card α
  simpa only [Nat.card_eq_fintype_card, ge_iff_le] using Fintype.card_le_of_surjective f hf
  -- 🎉 no goals
#align finite.card_le_of_surjective Finite.card_le_of_surjective

theorem card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card α = 0 ↔ IsEmpty α
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  -- 🎉 no goals
#align finite.card_eq_zero_iff Finite.card_eq_zero_iff

/-- If `f` is injective, then `Nat.card α ≤ Nat.card β`. We must also assume
  `Nat.card β = 0 → Nat.card α = 0` since `Nat.card` is defined to be `0` for infinite types. -/
theorem card_le_of_injective' {f : α → β} (hf : Function.Injective f)
    (h : Nat.card β = 0 → Nat.card α = 0) : Nat.card α ≤ Nat.card β :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h zero_le') fun h =>
    @card_le_of_injective α β (Nat.finite_of_card_ne_zero h) f hf
#align finite.card_le_of_injective' Finite.card_le_of_injective'

/-- If `f` is an embedding, then `Nat.card α ≤ Nat.card β`. We must also assume
  `Nat.card β = 0 → Nat.card α = 0` since `Nat.card` is defined to be `0` for infinite types. -/
theorem card_le_of_embedding' (f : α ↪ β) (h : Nat.card β = 0 → Nat.card α = 0) :
    Nat.card α ≤ Nat.card β :=
  card_le_of_injective' f.2 h
#align finite.card_le_of_embedding' Finite.card_le_of_embedding'

/-- If `f` is surjective, then `Nat.card β ≤ Nat.card α`. We must also assume
  `Nat.card α = 0 → Nat.card β = 0` since `Nat.card` is defined to be `0` for infinite types. -/
theorem card_le_of_surjective' {f : α → β} (hf : Function.Surjective f)
    (h : Nat.card α = 0 → Nat.card β = 0) : Nat.card β ≤ Nat.card α :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h zero_le') fun h =>
    @card_le_of_surjective α β (Nat.finite_of_card_ne_zero h) f hf
#align finite.card_le_of_surjective' Finite.card_le_of_surjective'

/-- NB: `Nat.card` is defined to be `0` for infinite types. -/
theorem card_eq_zero_of_surjective {f : α → β} (hf : Function.Surjective f) (h : Nat.card β = 0) :
    Nat.card α = 0 := by
  cases finite_or_infinite β
  -- ⊢ Nat.card α = 0
  · haveI := card_eq_zero_iff.mp h
    -- ⊢ Nat.card α = 0
    haveI := Function.isEmpty f
    -- ⊢ Nat.card α = 0
    exact Nat.card_of_isEmpty
    -- 🎉 no goals
  · haveI := Infinite.of_surjective f hf
    -- ⊢ Nat.card α = 0
    exact Nat.card_eq_zero_of_infinite
    -- 🎉 no goals
#align finite.card_eq_zero_of_surjective Finite.card_eq_zero_of_surjective

/-- NB: `Nat.card` is defined to be `0` for infinite types. -/
theorem card_eq_zero_of_injective [Nonempty α] {f : α → β} (hf : Function.Injective f)
    (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_surjective (Function.invFun_surjective hf) h
#align finite.card_eq_zero_of_injective Finite.card_eq_zero_of_injective

/-- NB: `Nat.card` is defined to be `0` for infinite types. -/
theorem card_eq_zero_of_embedding [Nonempty α] (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_injective f.2 h
#align finite.card_eq_zero_of_embedding Finite.card_eq_zero_of_embedding

theorem card_sum [Finite α] [Finite β] : Nat.card (Sum α β) = Nat.card α + Nat.card β := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card (α ⊕ β) = Nat.card α + Nat.card β
  haveI := Fintype.ofFinite β
  -- ⊢ Nat.card (α ⊕ β) = Nat.card α + Nat.card β
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum]
  -- 🎉 no goals
#align finite.card_sum Finite.card_sum

theorem card_image_le {s : Set α} [Finite s] (f : α → β) : Nat.card (f '' s) ≤ Nat.card s :=
  card_le_of_surjective _ Set.surjective_onto_image
#align finite.card_image_le Finite.card_image_le

theorem card_range_le [Finite α] (f : α → β) : Nat.card (Set.range f) ≤ Nat.card α :=
  card_le_of_surjective _ Set.surjective_onto_range
#align finite.card_range_le Finite.card_range_le

theorem card_subtype_le [Finite α] (p : α → Prop) : Nat.card { x // p x } ≤ Nat.card α := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card { x // p x } ≤ Nat.card α
  simpa only [Nat.card_eq_fintype_card, ge_iff_le] using Fintype.card_subtype_le p
  -- 🎉 no goals
#align finite.card_subtype_le Finite.card_subtype_le

theorem card_subtype_lt [Finite α] {p : α → Prop} {x : α} (hx : ¬p x) :
    Nat.card { x // p x } < Nat.card α := by
  haveI := Fintype.ofFinite α
  -- ⊢ Nat.card { x // p x } < Nat.card α
  simpa only [Nat.card_eq_fintype_card, gt_iff_lt] using Fintype.card_subtype_lt hx
  -- 🎉 no goals
#align finite.card_subtype_lt Finite.card_subtype_lt

end Finite

namespace PartENat

theorem card_eq_coe_nat_card (α : Type*) [Finite α] : card α = Nat.card α := by
  unfold PartENat.card
  -- ⊢ ↑Cardinal.toPartENat (Cardinal.mk α) = ↑(Nat.card α)
  apply symm
  -- ⊢ ↑(Nat.card α) = ↑Cardinal.toPartENat (Cardinal.mk α)
  rw [Cardinal.natCast_eq_toPartENat_iff]
  -- ⊢ ↑(Nat.card α) = Cardinal.mk α
  exact Finite.cast_card_eq_mk
  -- 🎉 no goals
#align part_enat.card_of_finite PartENat.card_eq_coe_nat_card

end PartENat

namespace Set

theorem card_union_le (s t : Set α) : Nat.card (↥(s ∪ t)) ≤ Nat.card s + Nat.card t := by
  cases' _root_.finite_or_infinite (↥(s ∪ t)) with h h
  -- ⊢ Nat.card ↑(s ∪ t) ≤ Nat.card ↑s + Nat.card ↑t
  · rw [finite_coe_iff, finite_union, ← finite_coe_iff, ← finite_coe_iff] at h
    -- ⊢ Nat.card ↑(s ∪ t) ≤ Nat.card ↑s + Nat.card ↑t
    cases h
    -- ⊢ Nat.card ↑(s ∪ t) ≤ Nat.card ↑s + Nat.card ↑t
    rw [← Cardinal.natCast_le, Nat.cast_add, Finite.cast_card_eq_mk, Finite.cast_card_eq_mk,
      Finite.cast_card_eq_mk]
    exact Cardinal.mk_union_le s t
    -- 🎉 no goals
  · exact Nat.card_eq_zero_of_infinite.trans_le (zero_le _)
    -- 🎉 no goals
#align set.card_union_le Set.card_union_le

end Set

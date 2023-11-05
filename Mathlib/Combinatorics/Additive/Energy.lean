/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod

#align_import combinatorics.additive.energy from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (λ x : (α × α) × α × α, x.1.1 * x.2.1 = x.1.2 * x.2.2)` (whose `card`
is `multiplicativeEnergy s t`) as a standalone definition.
-/


section

variable {α : Type*} [PartialOrder α] {x y : α}

end

variable {α : Type*} [DecidableEq α]

namespace Finset

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}
/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
@[to_additive additiveEnergy
      "The additive energy of two finsets `s` and `t` in a group is the
      number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`."]
def multiplicativeEnergy (s t : Finset α) : ℕ :=
  (((s ×ˢ s) ×ˢ t ×ˢ t).filter fun x : (α × α) × α × α => x.1.1 * x.2.1 = x.1.2 * x.2.2).card

@[to_additive additiveEnergy_mono]
theorem multiplicativeEnergy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
    multiplicativeEnergy s₁ t₁ ≤ multiplicativeEnergy s₂ t₂ :=
  card_le_of_subset <|
    filter_subset_filter _ <|
      product_subset_product (product_subset_product hs hs) <| product_subset_product ht ht

@[to_additive additiveEnergy_mono_left]
theorem multiplicativeEnergy_mono_left (hs : s₁ ⊆ s₂) :
    multiplicativeEnergy s₁ t ≤ multiplicativeEnergy s₂ t :=
  multiplicativeEnergy_mono hs Subset.rfl

@[to_additive additiveEnergy_mono_right]
theorem multiplicativeEnergy_mono_right (ht : t₁ ⊆ t₂) :
    multiplicativeEnergy s t₁ ≤ multiplicativeEnergy s t₂ :=
  multiplicativeEnergy_mono Subset.rfl ht

@[to_additive le_additiveEnergy]
theorem le_multiplicativeEnergy : s.card * t.card ≤ multiplicativeEnergy s t := by
  rw [← card_product]
  refine'
    card_le_card_of_inj_on (@fun x => ((x.1, x.1), x.2, x.2)) (by
    -- porting note: changed this from a `simp` proof without `only` because of a timeout
      simp only [ ← and_imp, mem_product, and_imp, Prod.forall, mem_filter,
        and_self, and_true, imp_self, implies_true]) fun a _ b _ => _
  simp only [Prod.mk.inj_iff, and_self_iff, and_imp]
  exact Prod.ext

@[to_additive additiveEnergy_pos]
theorem multiplicativeEnergy_pos (hs : s.Nonempty) (ht : t.Nonempty) :
    0 < multiplicativeEnergy s t :=
  (mul_pos hs.card_pos ht.card_pos).trans_le le_multiplicativeEnergy

variable (s t)

@[to_additive (attr := simp) additiveEnergy_empty_left]
theorem multiplicativeEnergy_empty_left : multiplicativeEnergy ∅ t = 0 := by
  simp [multiplicativeEnergy]

@[to_additive (attr := simp) additiveEnergy_empty_right]
theorem multiplicativeEnergy_empty_right : multiplicativeEnergy s ∅ = 0 := by
  simp [multiplicativeEnergy]

variable {s t}

@[to_additive (attr := simp) additiveEnergy_pos_iff]
theorem multiplicativeEnergy_pos_iff : 0 < multiplicativeEnergy s t ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h =>
    of_not_not fun H => by
      simp_rw [not_and_or, not_nonempty_iff_eq_empty] at H
      obtain rfl | rfl := H <;> simp [Nat.not_lt_zero] at h,
    fun h => multiplicativeEnergy_pos h.1 h.2⟩

@[to_additive (attr := simp) additive_energy_eq_zero_iff]
theorem multiplicativeEnergy_eq_zero_iff : multiplicativeEnergy s t = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← (Nat.zero_le _).not_gt_iff_eq, not_and_or, imp_iff_or_not, or_comm]

end Mul

section CommMonoid

variable [CommMonoid α]

@[to_additive additiveEnergy_comm]
theorem multiplicativeEnergy_comm (s t : Finset α) :
    multiplicativeEnergy s t = multiplicativeEnergy t s := by
  rw [multiplicativeEnergy, ← Finset.card_map (Equiv.prodComm _ _).toEmbedding, map_filter]
  simp [-Finset.card_map, eq_comm, multiplicativeEnergy, mul_comm, map_eq_image, Function.comp]

end CommMonoid

section CommGroup

variable [CommGroup α] [Fintype α] (s t : Finset α)

@[to_additive (attr := simp) additiveEnergy_univ_left]
theorem multiplicativeEnergy_univ_left :
    multiplicativeEnergy univ t = Fintype.card α * t.card ^ 2 := by
  simp only [multiplicativeEnergy, univ_product_univ, Fintype.card, sq, ← card_product]
  let f : α × α × α → (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f := by
    rintro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [Prod.ext_iff] at h
    obtain ⟨h, rfl, rfl⟩ := h
    rw [mul_right_cancel h.1]
  rw [← card_image_of_injOn this]
  congr with a
  simp only [mem_filter, mem_product, mem_univ, true_and_iff, mem_image, exists_prop,
    Prod.exists]
  refine' ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [mul_right_comm, h.2]⟩, _⟩
  rintro ⟨b, c, d, hcd, rfl⟩
  simpa [mul_right_comm]

@[to_additive (attr := simp) additiveEnergy_univ_right]
theorem multiplicativeEnergy_univ_right :
    multiplicativeEnergy s univ = Fintype.card α * s.card ^ 2 := by
  rw [multiplicativeEnergy_comm, multiplicativeEnergy_univ_left]

end CommGroup

end Finset

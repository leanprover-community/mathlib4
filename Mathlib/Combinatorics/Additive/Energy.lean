/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Pointwise

#align_import combinatorics.additive.energy from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (fun x : (α × α) × α × α ↦ x.1.1 * x.2.1 = x.1.2 * x.2.2)`
(whose `card` is `multiplicativeEnergy s t`) as a standalone definition.
-/

open scoped BigOperators Pointwise

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
#align finset.multiplicative_energy Finset.multiplicativeEnergy
#align finset.additive_energy Finset.additiveEnergy

@[inherit_doc multiplicativeEnergy] notation3:max "Eₘ[" s ", " t "]" => multiplicativeEnergy s t
@[inherit_doc additiveEnergy] notation3:max "E[" s ", " t "]" => additiveEnergy s t

/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
notation3:max "Eₘ[" s "]" => Finset.multiplicativeEnergy s s

/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
notation3:max "E[" s "]" => Finset.additiveEnergy s s

@[to_additive additiveEnergy_mono]
theorem multiplicativeEnergy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
    multiplicativeEnergy s₁ t₁ ≤ multiplicativeEnergy s₂ t₂ :=
  card_le_card <|
    filter_subset_filter _ <|
      product_subset_product (product_subset_product hs hs) <| product_subset_product ht ht
#align finset.multiplicative_energy_mono Finset.multiplicativeEnergy_mono
#align finset.additive_energy_mono Finset.additiveEnergy_mono

@[to_additive additiveEnergy_mono_left]
theorem multiplicativeEnergy_mono_left (hs : s₁ ⊆ s₂) :
    multiplicativeEnergy s₁ t ≤ multiplicativeEnergy s₂ t :=
  multiplicativeEnergy_mono hs Subset.rfl
#align finset.multiplicative_energy_mono_left Finset.multiplicativeEnergy_mono_left
#align finset.additive_energy_mono_left Finset.additiveEnergy_mono_left

@[to_additive additiveEnergy_mono_right]
theorem multiplicativeEnergy_mono_right (ht : t₁ ⊆ t₂) :
    multiplicativeEnergy s t₁ ≤ multiplicativeEnergy s t₂ :=
  multiplicativeEnergy_mono Subset.rfl ht
#align finset.multiplicative_energy_mono_right Finset.multiplicativeEnergy_mono_right
#align finset.additive_energy_mono_right Finset.additiveEnergy_mono_right

@[to_additive le_additiveEnergy]
theorem le_multiplicativeEnergy : s.card * t.card ≤ multiplicativeEnergy s t := by
  rw [← card_product]
  refine'
    card_le_card_of_inj_on (@fun x => ((x.1, x.1), x.2, x.2)) (by
    -- Porting note: changed this from a `simp` proof without `only` because of a timeout
      simp only [← and_imp, mem_product, Prod.forall, mem_filter, and_self, and_true, imp_self,
        implies_true]) fun a _ b _ => _
  simp only [Prod.mk.inj_iff, and_self_iff, and_imp]
  exact Prod.ext
#align finset.le_multiplicative_energy Finset.le_multiplicativeEnergy
#align finset.le_additive_energy Finset.le_additiveEnergy

@[to_additive additiveEnergy_pos]
theorem multiplicativeEnergy_pos (hs : s.Nonempty) (ht : t.Nonempty) :
    0 < multiplicativeEnergy s t :=
  (mul_pos hs.card_pos ht.card_pos).trans_le le_multiplicativeEnergy
#align finset.multiplicative_energy_pos Finset.multiplicativeEnergy_pos
#align finset.additive_energy_pos Finset.additiveEnergy_pos

variable (s t)

@[to_additive (attr := simp) additiveEnergy_empty_left]
theorem multiplicativeEnergy_empty_left : multiplicativeEnergy ∅ t = 0 := by
  simp [multiplicativeEnergy]
#align finset.multiplicative_energy_empty_left Finset.multiplicativeEnergy_empty_left
#align finset.additive_energy_empty_left Finset.additiveEnergy_empty_left

@[to_additive (attr := simp) additiveEnergy_empty_right]
theorem multiplicativeEnergy_empty_right : multiplicativeEnergy s ∅ = 0 := by
  simp [multiplicativeEnergy]
#align finset.multiplicative_energy_empty_right Finset.multiplicativeEnergy_empty_right
#align finset.additive_energy_empty_right Finset.additiveEnergy_empty_right

variable {s t}

@[to_additive (attr := simp) additiveEnergy_pos_iff]
theorem multiplicativeEnergy_pos_iff : 0 < multiplicativeEnergy s t ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h =>
    of_not_not fun H => by
      simp_rw [not_and_or, not_nonempty_iff_eq_empty] at H
      obtain rfl | rfl := H <;> simp [Nat.not_lt_zero] at h,
    fun h => multiplicativeEnergy_pos h.1 h.2⟩
#align finset.multiplicative_energy_pos_iff Finset.multiplicativeEnergy_pos_iff
#align finset.additive_energy_pos_iff Finset.additiveEnergy_pos_iff

@[to_additive (attr := simp) additive_energy_eq_zero_iff]
theorem multiplicativeEnergy_eq_zero_iff : multiplicativeEnergy s t = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← (Nat.zero_le _).not_gt_iff_eq, not_and_or, imp_iff_or_not, or_comm]
#align finset.multiplicative_energy_eq_zero_iff Finset.multiplicativeEnergy_eq_zero_iff
#align finset.additive_energy_eq_zero_iff Finset.additive_energy_eq_zero_iff

@[to_additive additiveEnergy_eq_card_filter]
lemma multiplicativeEnergy_eq_card_filter (s t : Finset α) :
    Eₘ[s, t] = (((s ×ˢ t) ×ˢ s ×ˢ t).filter fun ((a, b), c, d) ↦ a * b = c * d).card := by
  refine Finset.card_congr (fun ((a, b), c, d) _ ↦ ((a, c), b, d)) (by aesop) (by aesop)
    fun ((a, b), c, d) h ↦ ⟨((a, c), b, d), by simpa [and_and_and_comm] using h⟩

@[to_additive additiveEnergy_eq_sum_sq']
lemma multiplicativeEnergy_eq_sum_sq' (s t : Finset α) :
    Eₘ[s, t] = ∑ a in s * t, ((s ×ˢ t).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
  simp_rw [multiplicativeEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  -- The `swap`, `ext` and `simp` calls significantly reduce heartbeats
  swap
  · simp only [Set.PairwiseDisjoint, Set.Pairwise, coe_mul, ne_eq, disjoint_left, mem_product,
      mem_filter, not_and, and_imp, Prod.forall]
    aesop
  · congr
    ext
    simp only [mem_filter, mem_product, disjiUnion_eq_biUnion, mem_biUnion]
    aesop (add unsafe mul_mem_mul)

@[to_additive additiveEnergy_eq_sum_sq]
lemma multiplicativeEnergy_eq_sum_sq [Fintype α] (s t : Finset α) :
    Eₘ[s, t] = ∑ a, ((s ×ˢ t).filter fun (x, y) ↦ x * y = a).card ^ 2 := by
  rw [multiplicativeEnergy_eq_sum_sq']
  exact Fintype.sum_subset $ by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_additiveEnergy]
lemma card_sq_le_card_mul_multiplicativeEnergy (s t u : Finset α) :
    ((s ×ˢ t).filter fun (a, b) ↦ a * b ∈ u).card ^ 2 ≤ u.card * Eₘ[s, t] := by
  calc
    _ = (∑ c in u, ((s ×ˢ t).filter fun (a, b) ↦ a * b = c).card) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ ≤ u.card * ∑ c in u, ((s ×ˢ t).filter fun (a, b) ↦ a * b = c).card ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) _ 1 _
    _ ≤ u.card * ∑ c in s * t, ((s ×ˢ t).filter fun (a, b) ↦ a * b = c).card ^ 2 := by
        refine mul_le_mul_left' (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)
    _ = u.card * Eₘ[s, t] := by rw [multiplicativeEnergy_eq_sum_sq']

@[to_additive le_card_add_mul_additiveEnergy]
lemma le_card_add_mul_multiplicativeEnergy (s t : Finset α) :
    s.card ^ 2 * t.card ^ 2 ≤ (s * t).card * Eₘ[s, t] :=
  calc
    _ = ((s ×ˢ t).filter fun (a, b) ↦ a * b ∈ s * t).card ^ 2 := by
      rw [filter_eq_self.2, card_product, mul_pow]; aesop (add unsafe mul_mem_mul)
    _ ≤ (s * t).card * Eₘ[s, t] := card_sq_le_card_mul_multiplicativeEnergy _ _ _

end Mul

section CommMonoid

variable [CommMonoid α]

@[to_additive additiveEnergy_comm]
theorem multiplicativeEnergy_comm (s t : Finset α) :
    multiplicativeEnergy s t = multiplicativeEnergy t s := by
  rw [multiplicativeEnergy, ← Finset.card_map (Equiv.prodComm _ _).toEmbedding, map_filter]
  simp [-Finset.card_map, eq_comm, multiplicativeEnergy, mul_comm, map_eq_image, Function.comp]
#align finset.multiplicative_energy_comm Finset.multiplicativeEnergy_comm
#align finset.additive_energy_comm Finset.additiveEnergy_comm

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
  refine' ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [f, mul_right_comm, h.2]⟩, _⟩
  rintro ⟨b, c, d, hcd, rfl⟩
  simpa [mul_right_comm]
#align finset.multiplicative_energy_univ_left Finset.multiplicativeEnergy_univ_left
#align finset.additive_energy_univ_left Finset.additiveEnergy_univ_left

@[to_additive (attr := simp) additiveEnergy_univ_right]
theorem multiplicativeEnergy_univ_right :
    multiplicativeEnergy s univ = Fintype.card α * s.card ^ 2 := by
  rw [multiplicativeEnergy_comm, multiplicativeEnergy_univ_left]
#align finset.multiplicative_energy_univ_right Finset.multiplicativeEnergy_univ_right
#align finset.additive_energy_univ_right Finset.additiveEnergy_univ_right

end CommGroup

end Finset

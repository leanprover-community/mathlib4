/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## Main declarations

* `Finset.addEnergy`: The additive energy of two finsets in an additive group.
* `Finset.mulEnergy`: The multiplicative energy of two finsets in a group.

## Notation

The following notations are defined in the `Combinatorics.Additive` scope:
* `E[s, t]` for `Finset.addEnergy s t`.
* `Eₘ[s, t]` for `Finset.mulEnergy s t`.
* `E[s]` for `E[s, s]`.
* `Eₘ[s]` for `Eₘ[s, s]`.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (fun x : (α × α) × α × α ↦ x.1.1 * x.2.1 = x.1.2 * x.2.2)`
(whose `card` is `mulEnergy s t`) as a standalone definition.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset
section Mul
variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}

/-- The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of
quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`.

The notation `Eₘ[s, t]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`.

The notation `E[s, t]` is available in scope `Combinatorics.Additive`. -/]
def mulEnergy (s t : Finset α) : ℕ :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2}

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive] notation3:max "Eₘ[" s ", " t "]" => Finset.mulEnergy s t

/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive] notation3:max "E[" s ", " t "]" => Finset.addEnergy s t

/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive] notation3:max "Eₘ[" s "]" => Finset.mulEnergy s s

/-- The additive energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive] notation3:max "E[" s "]" => Finset.addEnergy s s

open scoped Combinatorics.Additive

@[to_additive (attr := gcongr)]
lemma mulEnergy_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : Eₘ[s₁, t₁] ≤ Eₘ[s₂, t₂] := by
  unfold mulEnergy; gcongr

@[to_additive] lemma mulEnergy_mono_left (hs : s₁ ⊆ s₂) : Eₘ[s₁, t] ≤ Eₘ[s₂, t] :=
  mulEnergy_mono hs Subset.rfl

@[to_additive] lemma mulEnergy_mono_right (ht : t₁ ⊆ t₂) : Eₘ[s, t₁] ≤ Eₘ[s, t₂] :=
  mulEnergy_mono Subset.rfl ht

@[to_additive] lemma le_mulEnergy : #s * #t ≤ Eₘ[s, t] := by
  rw [← card_product]
  exact card_le_card_of_injOn (fun x => ((x.1, x.1), x.2, x.2)) (by simp [Set.MapsTo]) (by simp)

@[to_additive] lemma le_mulEnergy_self : #s ^ 2 ≤ Eₘ[s] := sq #s ▸ le_mulEnergy

@[to_additive] lemma mulEnergy_pos (hs : s.Nonempty) (ht : t.Nonempty) : 0 < Eₘ[s, t] :=
  (mul_pos hs.card_pos ht.card_pos).trans_le le_mulEnergy

@[to_additive] lemma mulEnergy_self_pos (hs : s.Nonempty) : 0 < Eₘ[s] :=
  mulEnergy_pos hs hs

variable (s t)

@[to_additive (attr := simp)] lemma mulEnergy_empty_left : Eₘ[∅, t] = 0 := by simp [mulEnergy]

@[to_additive (attr := simp)] lemma mulEnergy_empty_right : Eₘ[s, ∅] = 0 := by simp [mulEnergy]

variable {s t}

@[to_additive (attr := simp)] lemma mulEnergy_pos_iff : 0 < Eₘ[s, t] ↔ s.Nonempty ∧ t.Nonempty where
  mp h := by by_contra! +distrib rfl | rfl <;> simp at h
  mpr h := mulEnergy_pos h.1 h.2

@[to_additive (attr := simp)] lemma mulEnergy_eq_zero_iff : Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← (Nat.zero_le _).not_lt_iff_eq', imp_iff_or_not, or_comm]

@[to_additive] lemma mulEnergy_self_pos_iff : 0 < Eₘ[s] ↔ s.Nonempty := by
  rw [mulEnergy_pos_iff, and_self_iff]

@[to_additive] lemma mulEnergy_self_eq_zero_iff : Eₘ[s] = 0 ↔ s = ∅ := by
  rw [mulEnergy_eq_zero_iff, or_self_iff]

@[to_additive] lemma mulEnergy_eq_card_filter (s t : Finset α) :
    Eₘ[s, t] = #{x ∈ ((s ×ˢ t) ×ˢ s ×ˢ t) | x.1.1 * x.1.2 = x.2.1 * x.2.2} :=
  card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

@[to_additive] lemma mulEnergy_eq_sum_sq' (s t : Finset α) :
    Eₘ[s, t] = ∑ a ∈ s * t, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = a} ^ 2 := by
  simp_rw [mulEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)

@[to_additive] lemma mulEnergy_eq_sum_sq [Fintype α] (s t : Finset α) :
    Eₘ[s, t] = ∑ a, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = a} ^ 2 := by
  rw [mulEnergy_eq_sum_sq']
  exact Fintype.sum_subset <| by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_addEnergy]
lemma card_sq_le_card_mul_mulEnergy (s t u : Finset α) :
    #{xy ∈ s ×ˢ t | xy.1 * xy.2 ∈ u} ^ 2 ≤ #u * Eₘ[s, t] := by
  calc
    _ = (∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ ≤ #u * ∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) _ 1 _
    _ ≤ #u * ∑ c ∈ s * t, #{xy ∈ s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        refine mul_le_mul_right (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)
    _ = #u * Eₘ[s, t] := by rw [mulEnergy_eq_sum_sq']

@[to_additive le_card_add_mul_addEnergy] lemma le_card_mul_mul_mulEnergy (s t : Finset α) :
    #s ^ 2 * #t ^ 2 ≤ #(s * t) * Eₘ[s, t] :=
  calc
    _ = #{xy ∈ s ×ˢ t | xy.1 * xy.2 ∈ s * t} ^ 2 := by
      rw [filter_eq_self.2, card_product, mul_pow]; aesop (add unsafe mul_mem_mul)
    _ ≤ #(s * t) * Eₘ[s, t] := card_sq_le_card_mul_mulEnergy _ _ _

end Mul

open scoped Combinatorics.Additive

section CommMonoid

variable [CommMonoid α]

@[to_additive] lemma mulEnergy_comm (s t : Finset α) : Eₘ[s, t] = Eₘ[t, s] := by
  rw [mulEnergy, ← Finset.card_map (Equiv.prodComm _ _).toEmbedding, map_filter]
  simp [-Finset.card_map, mulEnergy, mul_comm, map_eq_image, Function.comp_def]

end CommMonoid

section CommGroup

variable [CommGroup α] [Fintype α] (s t : Finset α)

@[to_additive (attr := simp)]
lemma mulEnergy_univ_left : Eₘ[univ, t] = Fintype.card α * t.card ^ 2 := by
  simp only [mulEnergy, univ_product_univ, Fintype.card, sq, ← card_product]
  let f : α × α × α → (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f := by
    rintro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [f, Prod.ext_iff] at h
    obtain ⟨h, rfl, rfl⟩ := h
    rw [mul_right_cancel h.1]
  rw [← card_image_of_injOn this]
  congr with a
  simp only [mem_filter, mem_product, mem_univ, true_and, mem_image,
    Prod.exists]
  refine ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [f, mul_right_comm, h.2]⟩, ?_⟩
  rintro ⟨b, c, d, hcd, rfl⟩
  simpa [f, mul_right_comm]

@[to_additive (attr := simp)]
lemma mulEnergy_univ_right : Eₘ[s, univ] = Fintype.card α * s.card ^ 2 := by
  rw [mulEnergy_comm, mulEnergy_univ_left]

end CommGroup

end Finset

/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Sups
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions" of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`, by making explicit the correction
term.

For a set family `𝒜` over a ground set of size `n`, the Ahlswede-Zhang identity states that the sum
of `|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|)` over all sets `A` is exactly `1`. This implies the LYM
inequality since for an antichain `𝒜` and every `A ∈ 𝒜` we have
`|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|) = 1 / n.choose |A|`.

## Main declarations

* `Finset.truncatedSup`: `s.truncatedSup a` is the supremum of all `b ≥ a` in `𝒜` if there are
  some, or `⊤` if there are none.
* `Finset.truncatedInf`: `s.truncatedInf a` is the infimum of all `b ≤ a` in `𝒜` if there are
  some, or `⊥` if there are none.
* `AhlswedeZhang.infSum`: LHS of the Ahlswede-Zhang identity.
* `AhlswedeZhang.le_infSum`: The sum of `1 / n.choose |A|` over an antichain is less than the RHS of
  the Ahlswede-Zhang identity.
* `AhlswedeZhang.infSum_eq_one`: Ahlswede-Zhang identity.

## References

* [R. Ahlswede, Z. Zhang, *An identity in combinatorial extremal theory*](https://doi.org/10.1016/0001-8708(90)90023-G)
* [D. T. Tru, *An AZ-style identity and Bollobás deficiency*](https://doi.org/10.1016/j.jcta.2007.03.005)
-/

@[expose] public section

section
variable (α : Type*) [Fintype α] [Nonempty α] {m n : ℕ}

open Finset Fintype Nat

private lemma binomial_sum_eq (h : n < m) :
    ∑ i ∈ range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 := by
  set f : ℕ → ℚ := fun i ↦ n.choose i * (m.choose i : ℚ)⁻¹ with hf
  suffices ∀ i ∈ range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this, sum_range_sub', hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : ℚ) ≠ 0 := i.cast_add_one_ne_zero
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq m i)
  push_cast at this
  dsimp [f, hf]
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq n i)
  push_cast at this
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have : (m - i : ℚ) ≠ 0 := sub_ne_zero_of_ne (cast_lt.mpr h₂).ne'
  have : (m.choose i : ℚ) ≠ 0 := cast_ne_zero.2 (choose_pos h₂.le).ne'
  simp [field, *]

private lemma Fintype.sum_div_mul_card_choose_card :
    ∑ s : Finset α, (card α / ((card α - #s) * (card α).choose #s) : ℚ) =
      card α * ∑ k ∈ range (card α), (↑k)⁻¹ + 1 := by
  rw [← powerset_univ, powerset_card_disjiUnion, sum_disjiUnion]
  have : ∀ {x : ℕ}, ∀ s ∈ powersetCard x (univ : Finset α),
    (card α / ((card α - #s) * (card α).choose #s) : ℚ) =
      card α / ((card α - x) * (card α).choose x) := by
    intro n s hs
    rw [mem_powersetCard_univ.1 hs]
  simp_rw [Finset.sum_congr rfl this, sum_const, card_powersetCard, card_univ, nsmul_eq_mul,
    mul_div, mul_comm, ← mul_div]
  rw [← mul_sum, ← mul_inv_cancel₀ (cast_ne_zero.mpr card_ne_zero : (card α : ℚ) ≠ 0), ← mul_add,
    add_comm _ ((card α)⁻¹ : ℚ), ← sum_insert (f := fun x : ℕ ↦ (x⁻¹ : ℚ)) notMem_range_self,
    ← range_add_one]
  have (n) (hn : n ∈ range (card α + 1)) :
      ((card α).choose n / ((card α - n) * (card α).choose n) : ℚ) = (card α - n : ℚ)⁻¹ := by
    rw [div_mul_cancel_right₀]
    exact cast_ne_zero.2 (choose_pos <| mem_range_succ_iff.1 hn).ne'
  simp only [Finset.sum_congr rfl this, mul_eq_mul_left_iff, cast_eq_zero]
  convert Or.inl <| sum_range_reflect _ _ with a ha
  rw [add_tsub_cancel_right, cast_sub (mem_range_succ_iff.mp ha)]

end

open scoped FinsetFamily

namespace Finset
variable {α β : Type*}

/-! ### Truncated supremum, truncated infimum -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] [BoundedOrder β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in
private lemma sup_aux [DecidableLE α] : a ∈ lowerClosure s → {b ∈ s | a ≤ b}.Nonempty :=
  fun ⟨b, hb, hab⟩ ↦ ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

private lemma lower_aux [DecidableEq α] :
    a ∈ lowerClosure ↑(s ∪ t) ↔ a ∈ lowerClosure s ∨ a ∈ lowerClosure t := by
  rw [coe_union, lowerClosure_union, LowerSet.mem_sup_iff]

variable [DecidableLE α] [OrderTop α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The supremum of the elements of `s` less than `a` if there are some, otherwise `⊤`. -/
def truncatedSup (s : Finset α) (a : α) : α :=
  if h : a ∈ lowerClosure s then {b ∈ s | a ≤ b}.sup' (sup_aux h) id else ⊤

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma truncatedSup_of_mem (h : a ∈ lowerClosure s) :
    truncatedSup s a = {b ∈ s | a ≤ b}.sup' (sup_aux h) id := dif_pos h

lemma truncatedSup_of_notMem (h : a ∉ lowerClosure s) : truncatedSup s a = ⊤ := dif_neg h

@[simp] lemma truncatedSup_empty (a : α) : truncatedSup ∅ a = ⊤ := truncatedSup_of_notMem (by simp)

@[simp] lemma truncatedSup_singleton (b a : α) : truncatedSup {b} a = if a ≤ b then b else ⊤ := by
  simp [truncatedSup]; split_ifs <;> simp [Finset.filter_true_of_mem, *]

lemma le_truncatedSup : a ≤ truncatedSup s a := by
  rw [truncatedSup]
  split_ifs with h
  · obtain ⟨ℬ, hb, h⟩ := h
    exact h.trans <| le_sup' id <| mem_filter.2 ⟨hb, h⟩
  · exact le_top

lemma map_truncatedSup [DecidableLE β] (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedSup s a) = truncatedSup (s.map e.toEquiv.toEmbedding) (e a) := by
  have : e a ∈ lowerClosure (s.map e.toEquiv.toEmbedding : Set β) ↔ a ∈ lowerClosure s := by simp
  simp_rw [truncatedSup, apply_dite e, map_finset_sup', map_top, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, sup'_map]

lemma truncatedSup_of_isAntichain (hs : IsAntichain (· ≤ ·) (s : Set α)) (ha : a ∈ s) :
    truncatedSup s a = a := by
  refine le_antisymm ?_ le_truncatedSup
  simp_rw [truncatedSup_of_mem (subset_lowerClosure ha), sup'_le_iff, mem_filter]
  rintro b ⟨hb, hab⟩
  exact (hs.eq ha hb hab).ge

variable [DecidableEq α]

lemma truncatedSup_union (hs : a ∈ lowerClosure s) (ht : a ∈ lowerClosure t) :
    truncatedSup (s ∪ t) a = truncatedSup s a ⊔ truncatedSup t a := by
  simpa only [truncatedSup_of_mem, hs, ht, lower_aux.2 (Or.inl hs), filter_union] using
    sup'_union _ _ _

lemma truncatedSup_union_left (hs : a ∈ lowerClosure s) (ht : a ∉ lowerClosure t) :
    truncatedSup (s ∪ t) a = truncatedSup s a := by
  simp only [mem_lowerClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedSup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (Or.inl hs)]

lemma truncatedSup_union_right (hs : a ∉ lowerClosure s) (ht : a ∈ lowerClosure t) :
    truncatedSup (s ∪ t) a = truncatedSup t a := by rw [union_comm, truncatedSup_union_left ht hs]

lemma truncatedSup_union_of_notMem (hs : a ∉ lowerClosure s) (ht : a ∉ lowerClosure t) :
    truncatedSup (s ∪ t) a = ⊤ := truncatedSup_of_notMem fun h ↦ (lower_aux.1 h).elim hs ht

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β]
  [BoundedOrder β] [DecidableLE β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in
private lemma inf_aux [DecidableLE α] : a ∈ upperClosure s → {b ∈ s | b ≤ a}.Nonempty :=
  fun ⟨b, hb, hab⟩ ↦ ⟨b, mem_filter.2 ⟨hb, hab⟩⟩

private lemma upper_aux [DecidableEq α] :
    a ∈ upperClosure ↑(s ∪ t) ↔ a ∈ upperClosure s ∨ a ∈ upperClosure t := by
  rw [coe_union, upperClosure_union, UpperSet.mem_inf_iff]

variable [DecidableLE α] [BoundedOrder α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncatedInf (s : Finset α) (a : α) : α :=
  if h : a ∈ upperClosure s then {b ∈ s | b ≤ a}.inf' (inf_aux h) id else ⊥

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma truncatedInf_of_mem (h : a ∈ upperClosure s) :
    truncatedInf s a = {b ∈ s | b ≤ a}.inf' (inf_aux h) id := dif_pos h

lemma truncatedInf_of_notMem (h : a ∉ upperClosure s) : truncatedInf s a = ⊥ := dif_neg h

lemma truncatedInf_le : truncatedInf s a ≤ a := by
  unfold truncatedInf
  split_ifs with h
  · obtain ⟨b, hb, hba⟩ := h
    exact hba.trans' <| inf'_le id <| mem_filter.2 ⟨hb, ‹_›⟩
  · exact bot_le

@[simp] lemma truncatedInf_empty (a : α) : truncatedInf ∅ a = ⊥ := truncatedInf_of_notMem (by simp)

@[simp] lemma truncatedInf_singleton (b a : α) : truncatedInf {b} a = if b ≤ a then b else ⊥ := by
  simp only [truncatedInf, coe_singleton, upperClosure_singleton, UpperSet.mem_Ici_iff,
    id_eq]
  split_ifs <;> simp [Finset.filter_true_of_mem, *]

lemma map_truncatedInf (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedInf s a) = truncatedInf (s.map e.toEquiv.toEmbedding) (e a) := by
  have : e a ∈ upperClosure (s.map e.toEquiv.toEmbedding) ↔ a ∈ upperClosure s := by simp
  simp_rw [truncatedInf, apply_dite e, map_finset_inf', map_bot, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, inf'_map]

lemma truncatedInf_of_isAntichain (hs : IsAntichain (· ≤ ·) (s : Set α)) (ha : a ∈ s) :
    truncatedInf s a = a := by
  refine le_antisymm truncatedInf_le ?_
  simp_rw [truncatedInf_of_mem (subset_upperClosure ha), le_inf'_iff, mem_filter]
  rintro b ⟨hb, hba⟩
  exact (hs.eq hb ha hba).ge

variable [DecidableEq α]

lemma truncatedInf_union (hs : a ∈ upperClosure s) (ht : a ∈ upperClosure t) :
    truncatedInf (s ∪ t) a = truncatedInf s a ⊓ truncatedInf t a := by
  simpa only [truncatedInf_of_mem, hs, ht, upper_aux.2 (Or.inl hs), filter_union] using
    inf'_union _ _ _

lemma truncatedInf_union_left (hs : a ∈ upperClosure s) (ht : a ∉ upperClosure t) :
    truncatedInf (s ∪ t) a = truncatedInf s a := by
  simp only [mem_upperClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedInf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (Or.inl hs)]

lemma truncatedInf_union_right (hs : a ∉ upperClosure s) (ht : a ∈ upperClosure t) :
    truncatedInf (s ∪ t) a = truncatedInf t a := by
  rw [union_comm, truncatedInf_union_left ht hs]

lemma truncatedInf_union_of_notMem (hs : a ∉ upperClosure s) (ht : a ∉ upperClosure t) :
    truncatedInf (s ∪ t) a = ⊥ :=
  truncatedInf_of_notMem <| by rw [coe_union, upperClosure_union]; exact fun h ↦ h.elim hs ht

end SemilatticeInf

section DistribLattice
variable [DistribLattice α] [DecidableEq α] {s t : Finset α} {a : α}

private lemma infs_aux : a ∈ lowerClosure ↑(s ⊼ t) ↔ a ∈ lowerClosure s ∧ a ∈ lowerClosure t := by
  rw [coe_infs, lowerClosure_infs, LowerSet.mem_inf_iff]

private lemma sups_aux : a ∈ upperClosure ↑(s ⊻ t) ↔ a ∈ upperClosure s ∧ a ∈ upperClosure t := by
  rw [coe_sups, upperClosure_sups, UpperSet.mem_sup_iff]

variable [DecidableLE α] [BoundedOrder α]

lemma truncatedSup_infs (hs : a ∈ lowerClosure s) (ht : a ∈ lowerClosure t) :
    truncatedSup (s ⊼ t) a = truncatedSup s a ⊓ truncatedSup t a := by
  simp only [truncatedSup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_le]
  simp_rw [← image_inf_product]
  rw [sup'_image]
  simp [Function.uncurry_def]

lemma truncatedInf_sups (hs : a ∈ upperClosure s) (ht : a ∈ upperClosure t) :
    truncatedInf (s ⊻ t) a = truncatedInf s a ⊔ truncatedInf t a := by
  simp only [truncatedInf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le]
  simp_rw [← image_sup_product]
  rw [inf'_image]
  simp [Function.uncurry_def]

lemma truncatedSup_infs_of_notMem (ha : a ∉ lowerClosure s ⊓ lowerClosure t) :
    truncatedSup (s ⊼ t) a = ⊤ :=
  truncatedSup_of_notMem <| by rwa [coe_infs, lowerClosure_infs]

lemma truncatedInf_sups_of_notMem (ha : a ∉ upperClosure s ⊔ upperClosure t) :
    truncatedInf (s ⊻ t) a = ⊥ :=
  truncatedInf_of_notMem <| by rwa [coe_sups, upperClosure_sups]

end DistribLattice

section BooleanAlgebra
variable [BooleanAlgebra α] [DecidableLE α]

@[simp] lemma compl_truncatedSup (s : Finset α) (a : α) :
    (truncatedSup s a)ᶜ = truncatedInf sᶜˢ aᶜ := map_truncatedSup (OrderIso.compl α) _ _

@[simp] lemma compl_truncatedInf (s : Finset α) (a : α) :
    (truncatedInf s a)ᶜ = truncatedSup sᶜˢ aᶜ := map_truncatedInf (OrderIso.compl α) _ _

end BooleanAlgebra

variable [DecidableEq α] [Fintype α]

lemma card_truncatedSup_union_add_card_truncatedSup_infs (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
    #(truncatedSup (𝒜 ∪ ℬ) s) + #(truncatedSup (𝒜 ⊼ ℬ) s) =
      #(truncatedSup 𝒜 s) + #(truncatedSup ℬ s) := by
  by_cases h𝒜 : s ∈ lowerClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s ∈ lowerClosure (ℬ : Set <| Finset α)
  · rw [truncatedSup_union h𝒜 hℬ, truncatedSup_infs h𝒜 hℬ]
    exact card_union_add_card_inter _ _
  · rw [truncatedSup_union_left h𝒜 hℬ, truncatedSup_of_notMem hℬ,
      truncatedSup_infs_of_notMem fun h ↦ hℬ h.2]
  · rw [truncatedSup_union_right h𝒜 hℬ, truncatedSup_of_notMem h𝒜,
      truncatedSup_infs_of_notMem fun h ↦ h𝒜 h.1, add_comm]
  · rw [truncatedSup_of_notMem h𝒜, truncatedSup_of_notMem hℬ,
      truncatedSup_union_of_notMem h𝒜 hℬ, truncatedSup_infs_of_notMem fun h ↦ h𝒜 h.1]

lemma card_truncatedInf_union_add_card_truncatedInf_sups (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
    #(truncatedInf (𝒜 ∪ ℬ) s) + #(truncatedInf (𝒜 ⊻ ℬ) s) =
      #(truncatedInf 𝒜 s) + #(truncatedInf ℬ s) := by
  by_cases h𝒜 : s ∈ upperClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s ∈ upperClosure (ℬ : Set <| Finset α)
  · rw [truncatedInf_union h𝒜 hℬ, truncatedInf_sups h𝒜 hℬ]
    exact card_inter_add_card_union _ _
  · rw [truncatedInf_union_left h𝒜 hℬ, truncatedInf_of_notMem hℬ,
      truncatedInf_sups_of_notMem fun h ↦ hℬ h.2]
  · rw [truncatedInf_union_right h𝒜 hℬ, truncatedInf_of_notMem h𝒜,
      truncatedInf_sups_of_notMem fun h ↦ h𝒜 h.1, add_comm]
  · rw [truncatedInf_of_notMem h𝒜, truncatedInf_of_notMem hℬ,
      truncatedInf_union_of_notMem h𝒜 hℬ, truncatedInf_sups_of_notMem fun h ↦ h𝒜 h.1]

end Finset

open Finset hiding card
open Fintype Nat

namespace AhlswedeZhang
variable {α : Type*} [Fintype α] [DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finset α}

/-- Weighted sum of the size of the truncated infima of a set family. Relevant to the
Ahlswede-Zhang identity. -/
def infSum (𝒜 : Finset (Finset α)) : ℚ :=
  ∑ s, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s)

/-- Weighted sum of the size of the truncated suprema of a set family. Relevant to the
Ahlswede-Zhang identity. -/
def supSum (𝒜 : Finset (Finset α)) : ℚ :=
  ∑ s, #(truncatedSup 𝒜 s) / ((card α - #s) * (card α).choose #s)

lemma supSum_union_add_supSum_infs (𝒜 ℬ : Finset (Finset α)) :
    supSum (𝒜 ∪ ℬ) + supSum (𝒜 ⊼ ℬ) = supSum 𝒜 + supSum ℬ := by
  unfold supSum
  rw [← sum_add_distrib, ← sum_add_distrib, Finset.sum_congr rfl fun s _ ↦ _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedSup_union_add_card_truncatedSup_infs]
  simp

lemma infSum_union_add_infSum_sups (𝒜 ℬ : Finset (Finset α)) :
    infSum (𝒜 ∪ ℬ) + infSum (𝒜 ⊻ ℬ) = infSum 𝒜 + infSum ℬ := by
  unfold infSum
  rw [← sum_add_distrib, ← sum_add_distrib, Finset.sum_congr rfl fun s _ ↦ _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedInf_union_add_card_truncatedInf_sups]
  simp

lemma IsAntichain.le_infSum (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) (h𝒜₀ : ∅ ∉ 𝒜) :
    ∑ s ∈ 𝒜, ((card α).choose #s : ℚ)⁻¹ ≤ infSum 𝒜 := by
  calc
    _ = ∑ s ∈ 𝒜, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s : ℚ) := ?_
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun s ↦ by positivity
  refine sum_congr rfl fun s hs ↦ ?_
  rw [truncatedInf_of_isAntichain h𝒜 hs, div_mul_cancel_left₀]
  have := (nonempty_iff_ne_empty.2 <| ne_of_mem_of_not_mem hs h𝒜₀).card_pos
  positivity

variable [Nonempty α]

@[simp] lemma supSum_singleton (hs : s ≠ univ) :
    supSum ({s} : Finset (Finset α)) = card α * ∑ k ∈ range (card α), (k : ℚ)⁻¹ := by
  have : ∀ t : Finset α,
    (card α - #(truncatedSup {s} t) : ℚ) / ((card α - #t) * (card α).choose #t) =
    if t ⊆ s then (card α - #s : ℚ) / ((card α - #t) * (card α).choose #t) else 0 := by
    rintro t
    simp_rw [truncatedSup_singleton, le_iff_subset]
    split_ifs <;> simp
  simp_rw [← sub_eq_of_eq_add (Fintype.sum_div_mul_card_choose_card α), eq_sub_iff_add_eq,
    ← eq_sub_iff_add_eq', supSum, ← sum_sub_distrib, ← sub_div]
  rw [sum_congr rfl fun t _ ↦ this t, sum_ite, sum_const_zero, add_zero, filter_subset_univ,
    sum_powerset, ← binomial_sum_eq ((card_lt_iff_ne_univ _).2 hs), eq_comm]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [mul_div_assoc, ← nsmul_eq_mul]
  exact sum_powersetCard n s fun m ↦ (card α - #s : ℚ) / ((card α - m) * (card α).choose m)

/-- The **Ahlswede-Zhang Identity**. -/
lemma infSum_compls_add_supSum (𝒜 : Finset (Finset α)) :
    infSum 𝒜ᶜˢ + supSum 𝒜 = card α * ∑ k ∈ range (card α), (k : ℚ)⁻¹ + 1 := by
  unfold infSum supSum
  rw [← @map_univ_of_surjective (Finset α) _ _ _ ⟨compl, compl_injective⟩ compl_surjective, sum_map]
  simp only [Function.Embedding.coeFn_mk, univ_map_embedding, ← compl_truncatedSup,
    ← sum_add_distrib, card_compl, cast_sub (card_le_univ _), choose_symm (card_le_univ _),
    ← add_div, sub_add_cancel, Fintype.sum_div_mul_card_choose_card]

lemma supSum_of_univ_notMem (h𝒜₁ : 𝒜.Nonempty) (h𝒜₂ : univ ∉ 𝒜) :
    supSum 𝒜 = card α * ∑ k ∈ range (card α), (k : ℚ)⁻¹ := by
  set m := 𝒜.card with hm
  clear_value m
  induction m using Nat.strongRecOn generalizing 𝒜 with | ind m ih => _
  replace ih := fun 𝒜 h𝒜 h𝒜₁ h𝒜₂ ↦ @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial
  · refine supSum_singleton ?_
    simpa [eq_comm] using h𝒜₂
  cases m
  · cases h𝒜₁.card_pos.ne hm
  obtain ⟨s, 𝒜, hs, rfl, rfl⟩ := card_eq_succ.1 hm.symm
  have h𝒜 : 𝒜.Nonempty := by by_contra! rfl; simp at h𝒜₃
  rw [insert_eq, eq_sub_of_add_eq (supSum_union_add_supSum_infs _ _), singleton_infs,
    supSum_singleton (ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂), ih, ih, add_sub_cancel_right]
  · exact card_image_le.trans_lt (lt_add_one _)
  · exact h𝒜.image _
  · simpa using fun _ ↦ ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂
  · exact lt_add_one _
  · exact h𝒜
  · exact fun h ↦ h𝒜₂ (mem_insert_of_mem h)

/-- The **Ahlswede-Zhang Identity**. -/
@[informal "Ahlswede-Zhang identity"]
lemma infSum_eq_one (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) : infSum 𝒜 = 1 := by
  rw [← compls_compls 𝒜, eq_sub_of_add_eq (infSum_compls_add_supSum _),
    supSum_of_univ_notMem h𝒜₁.compls, add_sub_cancel_left]
  simpa

end AhlswedeZhang

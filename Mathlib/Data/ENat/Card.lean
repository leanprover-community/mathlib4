/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum

/-!
Placeholder
-/

variable {α β : Type*}

lemma ENat.natCast_lt_add_right_iff (a : ℕ) {b : ℕ∞} : a < a + b ↔ b ≠ 0 := by
  cases b using ENat.recTopCoe with
  | top => simp
  | coe b => simp [← Nat.cast_add, Nat.ne_zero_iff_zero_lt]

lemma ENat.natCast_lt_add_left_iff (a : ℕ) {b : ℕ∞} : a < b + a ↔ b ≠ 0 := by
  rw [add_comm, ENat.natCast_lt_add_right_iff]

@[simp]
lemma ENat.lt_add_right_iff (a b : ℕ∞) : a < a + b ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  cases a using ENat.recTopCoe with
  | top => simp
  | coe a => simp [ENat.natCast_lt_add_right_iff]

@[simp]
lemma ENat.lt_add_left_iff (a b : ℕ∞) : a < b + a ↔ a ≠ ⊤ ∧ b ≠ 0 := by
  simp [add_comm]

lemma ENat.coe_lt_iff {a : ℕ} {b : ℕ∞} : a < b ↔ a + 1 ≤ b := by
  cases b using ENat.recTopCoe with
  | top => simp
  | coe b => norm_cast

lemma ENat.sSup_eq_top_iff {s : Set ℕ∞} : sSup s = ⊤ ↔ ∀ n : ℕ, ∃ x ∈ s, n ≤ x := by
  refine sSup_eq_top.trans ⟨fun h n ↦ ?_, fun h b hb ↦ ?_⟩
  · obtain ⟨a, has, hba⟩ := h n (by simp)
    exact ⟨_, has, hba.le⟩
  lift b to ℕ using hb.ne
  obtain ⟨x, hx, hbx⟩ := h (b+1)
  exact ⟨x, hx, ENat.coe_lt_iff.2 hbx⟩

namespace ENat


noncomputable def card' (α : Type*) : ℕ∞ := sSup ((↑) '' {n : ℕ | Nonempty (Fin n ↪ α)})

lemma nonempty_fintype_or_infinite (α : Type*) : Nonempty (Fintype α) ∨ Infinite α :=
  (finite_or_infinite α).elim (fun _ ↦ .inl ⟨Fintype.ofFinite α⟩) .inr

lemma Infinite.nonempty_fin_embedding (α : Type*) [h : Infinite α] (n : ℕ) :
    Nonempty (Fin n ↪ α) := by
  obtain ⟨s, rfl⟩ := h.exists_subset_card_eq _ n
  exact ⟨s.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype fun x ↦ x ∈ s)⟩

@[simp]
theorem card_eq_coe_fintypeCard (α : Type*) [Fintype α] : card' α = Fintype.card α := by
  refine (sSup_le ?_).antisymm <| le_sSup ⟨_, ⟨(Fintype.equivFin α).symm.toEmbedding⟩, rfl⟩
  rintro e ⟨n, ⟨φ⟩, rfl⟩
  simpa using Fintype.card_le_of_embedding <| φ.trans <| (Fintype.equivFin α).toEmbedding

@[simp high]
theorem card_eq_top_of_infinite (α : Type*) [Infinite α] : card' α = ⊤ := by
  suffices ∀ (n : ℕ), ∃ a, Nonempty (Fin a ↪ α) ∧ n ≤ a by simpa [card', sSup_eq_top_iff]
  exact fun n ↦ ⟨n, Infinite.nonempty_fin_embedding α n, rfl.le⟩

theorem _root_.Infinite.eNat_card_eq (hα : Infinite α) : card' α = ⊤ :=
  card_eq_top_of_infinite α

@[simp] lemma card_eq_top : card' α = ⊤ ↔ Infinite α := by
  refine ⟨fun h ↦ not_finite_iff_infinite.1 fun hfin ↦ ?_, fun h ↦ card_eq_top_of_infinite α⟩
  simp [@card_eq_coe_fintypeCard α (Fintype.ofFinite α)] at h

@[simp] theorem card_lt_top_of_finite [Finite α] : card' α < ⊤ := by
  simpa [lt_top_iff_ne_top, Ne]

lemma _root_.Function.Injective.eNat_card_le {f : α → β} (hf : Function.Injective f) :
    card' α ≤ card' β := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite β
  · have hα := @Fintype.ofFinite _ <| Finite.of_injective f hf
    rw [card_eq_coe_fintypeCard, card_eq_coe_fintypeCard, Nat.cast_le]
    exact Fintype.card_le_of_injective f hf
  simp

lemma _root_.Function.Embedding.eNat_card_le (f : α ↪ β) : card' α ≤ card' β :=
  f.injective.eNat_card_le

@[simp]
theorem card_sum (α β : Type*) : card' (α ⊕ β) = card' α + card' β := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite (α ⊕ β)
  · have hα := @Fintype.ofFinite α (Finite.sum_left β)
    have hβ := @Fintype.ofFinite β (Finite.sum_right α)
    simp only [card_eq_coe_fintypeCard, ← Nat.cast_add, Nat.cast_inj]
    convert @Fintype.card_sum α β hα hβ
  obtain h | h := infinite_sum.1 hinf <;>
  simp [card_eq_top_of_infinite]

theorem card_congr {α β : Type*} (f : α ≃ β) : card' α = card' β :=
   f.injective.eNat_card_le.antisymm f.symm.injective.eNat_card_le

@[simp] lemma card_ulift (α : Type*) : card' (ULift α) = card' α := card_congr Equiv.ulift

@[simp] lemma card_plift (α : Type*) : card' (PLift α) = card' α := card_congr Equiv.plift

theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card' (f '' s) = card' s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card' (f '' s) = card' s := card_image_of_injOn h.injOn

theorem card_eq_zero_iff_empty (α : Type*) : card' α = 0 ↔ IsEmpty α := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite α
  · rw [card_eq_coe_fintypeCard, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
  simp [hinf.eNat_card_eq]

theorem card_le_one_iff_subsingleton (α : Type*) : card' α ≤ 1 ↔ Subsingleton α := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite α
  · rw [card_eq_coe_fintypeCard, Nat.cast_le_one, Fintype.card_le_one_iff_subsingleton]
  exact iff_of_false (by simp [hinf.eNat_card_eq]) (not_subsingleton α)

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card' α ↔ Nontrivial α := by
  rw [← not_le, card_le_one_iff_subsingleton, not_subsingleton_iff_nontrivial]

end ENat

namespace Nat

end Nat

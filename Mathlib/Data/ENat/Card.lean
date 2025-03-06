import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum

variable {α : Type*}

namespace ENat

noncomputable def card (α : Type*) : ℕ∞ := sSup ((↑) '' {n : ℕ | Nonempty (Fin n ↪ α)})

lemma nonempty_fintype_or_infinite (α : Type*) : Nonempty (Fintype α) ∨ Infinite α :=
  (finite_or_infinite α).elim (fun _ ↦ .inl ⟨Fintype.ofFinite α⟩) .inr

lemma Infinite.nonempty_fin_embedding (α : Type*) [h : Infinite α] (n : ℕ) :
    Nonempty (Fin n ↪ α) := by
  obtain ⟨s, rfl⟩ := h.exists_subset_card_eq _ n
  exact ⟨s.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype fun x ↦ x ∈ s)⟩

@[simp]
theorem card_eq_coe_fintype_card (α : Type*) [Fintype α] : card α = Fintype.card α := by
  refine le_antisymm (sSup_le ?_) <|
    le_sSup ⟨Fintype.card α, ⟨(Fintype.equivFin α).symm.toEmbedding⟩, rfl⟩
  rintro e ⟨n, ⟨φ⟩, rfl⟩
  simpa using Fintype.card_le_of_embedding <| φ.trans <| (Fintype.equivFin α).toEmbedding

@[simp high]
theorem card_eq_top_of_infinite (α : Type*) [Infinite α] : card α = ⊤ := by
  refine sSup_eq_top.2 fun n hn ↦ ?_
  lift n to ℕ using hn.ne
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and, Nat.cast_lt]
  exact ⟨n+1, Infinite.nonempty_fin_embedding α _, by simp⟩

theorem _root_.Infinite.eNat_card_eq (hα : Infinite α) : card α = ⊤ :=
  card_eq_top_of_infinite α

@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by
  refine ⟨fun h ↦ not_finite_iff_infinite.1 fun hfin ↦ ?_, fun h ↦ card_eq_top_of_infinite α⟩
  simp [@card_eq_coe_fintype_card α (Fintype.ofFinite α)] at h

@[simp] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by
  simpa [lt_top_iff_ne_top, Ne]

@[simp]
theorem card_sum (α β : Type*) : card (α ⊕ β) = card α + card β := by
  obtain hfin | hinf := finite_or_infinite (α ⊕ β)
  · have hα := @Fintype.ofFinite α (Finite.sum_left β)
    have hβ := @Fintype.ofFinite β (Finite.sum_right α)
    simp only [card_eq_coe_fintype_card, ← Nat.cast_add, Nat.cast_inj]
    exact @Fintype.card_sum α β hα hβ
  obtain h | h := infinite_sum.1 hinf <;>
  simp [card_eq_top_of_infinite]

theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β := by
  obtain hfin | hinf := finite_or_infinite α
  · have := Fintype.ofFinite α
    have := @Fintype.ofFinite _ ((Equiv.finite_iff f).1 hfin)
    rw [card_eq_coe_fintype_card, card_eq_coe_fintype_card, Nat.cast_inj]
    exact Fintype.card_congr f
  rw [hinf.eNat_card_eq, ((Equiv.infinite_iff f).1 hinf).eNat_card_eq]

@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

theorem card_image_of_injOn {α β : Type*} {f : α → β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

theorem card_image_of_injective {α β : Type*} (f : α → β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite α
  · rw [card_eq_coe_fintype_card, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
  simp [hinf.eNat_card_eq]

theorem card_le_one_iff_subsingleton (α : Type*) : card α ≤ 1 ↔ Subsingleton α := by
  obtain ⟨⟨hfin⟩⟩ | hinf := nonempty_fintype_or_infinite α
  · rw [card_eq_coe_fintype_card, Nat.cast_le_one, Fintype.card_le_one_iff_subsingleton]
  exact iff_of_false (by simp [hinf.eNat_card_eq]) (not_subsingleton α)

theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← not_le, card_le_one_iff_subsingleton, not_subsingleton_iff_nontrivial]

end ENat

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Interval.Finset.Defs

/-!
# `Filter.atTop` and `Filter.atBot` filters and finite sets.
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

theorem tendsto_finset_range : Tendsto Finset.range atTop atTop :=
  Finset.range_mono.tendsto_atTop_atTop Finset.exists_nat_subset_range

theorem atTop_finset_eq_iInf : (atTop : Filter (Finset α)) = ⨅ x : α, 𝓟 (Ici {x}) := by
  refine le_antisymm (le_iInf fun i => le_principal_iff.2 <| mem_atTop ({i} : Finset α)) ?_
  refine
    le_iInf fun s =>
      le_principal_iff.2 <| mem_iInf_of_iInter s.finite_toSet (fun i => mem_principal_self _) ?_
  simp only [subset_def, mem_iInter, SetCoe.forall, mem_Ici,
    Finset.mem_singleton, Finset.subset_iff, forall_eq]
  exact fun t => id

/-- If `f` is a monotone sequence of `Finset`s and each `x` belongs to one of `f n`, then
`Tendsto f atTop atTop`. -/
theorem tendsto_atTop_finset_of_monotone [Preorder β] {f : β → Finset α} (h : Monotone f)
    (h' : ∀ x : α, ∃ n, x ∈ f n) : Tendsto f atTop atTop := by
  simp only [atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
  intro a
  rcases h' a with ⟨b, hb⟩
  exact (eventually_ge_atTop b).mono fun b' hb' => (Finset.singleton_subset_iff.2 hb).trans (h hb')

alias _root_.Monotone.tendsto_atTop_finset := tendsto_atTop_finset_of_monotone

theorem tendsto_finset_image_atTop_atTop [DecidableEq β] {i : β → γ} {j : γ → β}
    (h : Function.LeftInverse j i) : Tendsto (Finset.image j) atTop atTop :=
  (Finset.image_mono j).tendsto_atTop_finset fun a =>
    ⟨{i a}, by simp only [Finset.image_singleton, h a, Finset.mem_singleton]⟩

theorem tendsto_finset_preimage_atTop_atTop {f : α → β} (hf : Function.Injective f) :
    Tendsto (fun s : Finset β => s.preimage f (hf.injOn)) atTop atTop :=
  (Finset.monotone_preimage hf).tendsto_atTop_finset fun x =>
    ⟨{f x}, Finset.mem_preimage.2 <| Finset.mem_singleton_self _⟩

lemma tendsto_toLeft_atTop :
    Tendsto (Finset.toLeft (α := α) (β := β)) atTop atTop := by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨t.disjSum ∅, fun b hb ↦ H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

lemma tendsto_toRight_atTop :
    Tendsto (Finset.toRight (α := α) (β := β)) atTop atTop := by
  intro s hs
  simp only [mem_atTop_sets, Filter.mem_map, Set.mem_preimage] at hs ⊢
  obtain ⟨t, H⟩ := hs
  exact ⟨.disjSum ∅ t, fun b hb ↦ H _ (by simpa [← Finset.coe_subset, Set.subset_def] using hb)⟩

theorem tendsto_finset_powerset_atTop_atTop : Tendsto (Finset.powerset (α := α)) atTop atTop := by
  classical
  refine tendsto_atTop_atTop.mpr fun t ↦ ⟨t.sup id, fun _ hu _ hv ↦ ?_⟩
  exact Finset.mem_powerset.mpr <| (Finset.le_sup_of_le hv fun _ h ↦ h).trans hu

theorem tendsto_finset_Iic_atTop_atTop [Preorder α] [LocallyFiniteOrderBot α] :
    Tendsto (Finset.Iic (α := α)) atTop atTop := by
  rcases isEmpty_or_nonempty α with _ | _
  · exact tendsto_of_isEmpty
  by_cases h : IsDirectedOrder α
  · refine tendsto_atTop_atTop.mpr fun s ↦ ?_
    obtain ⟨a, ha⟩ := Finset.exists_le s
    exact ⟨a, fun b hb c hc ↦ by simpa using (ha c hc).trans hb⟩
  · obtain h := Filter.atTop_neBot_iff.not.mpr (fun h' ↦ h h'.2)
    simp [not_ne_iff.mp <| Filter.neBot_iff.not.mp h]

theorem tendsto_finset_Ici_atBot_atTop [Preorder α] [LocallyFiniteOrderTop α] :
    Tendsto (Finset.Ici (α := α)) atBot atTop :=
  tendsto_finset_Iic_atTop_atTop (α := αᵒᵈ)

section Card

/-- Every finset is eventually a subset of `s` along `atTop`. -/
lemma eventually_finset_atTop_subset (i : Finset α) : ∀ᶠ s : Finset α in atTop, i ⊆ s :=
  eventually_ge_atTop _

/-- Every element of `α` is eventually a member of `s` along `atTop` on `Finset α`. -/
lemma eventually_finset_mem_atTop (i : α) : ∀ᶠ s : Finset α in atTop, i ∈ s := by
  simpa using eventually_finset_atTop_subset {i}

/-- The pushforward of `atTop` on `Finset α` along `Finset.card` is `atTop` on `ℕ`, when `α` is
infinite. -/
lemma map_card_atTop [Infinite α] :
    map (Finset.card (α := α)) atTop = atTop := by
  rw [map_atTop_eq, atTop]
  refine Function.Surjective.iInf_congr Finset.card Finset.exists_card_eq fun s ↦ congr(𝓟 $(?_))
  ext
  refine ⟨Infinite.exists_superset_card_eq _ _, ?_⟩
  aesop (add safe apply Finset.card_le_card)

/-- The pushforward of `atTop` on `Finset α` along `Finset.card` is `pure (Fintype.card α)`, when
`α` is finite. -/
lemma map_card_atTop_of_fintype [Fintype α] :
    map (Finset.card : Finset α → ℕ) atTop = pure (Fintype.card α) := by
  simp [OrderTop.atTop_eq]

/-- `Finset.card` tends to `atTop` along `atTop` on `Finset α`, when `α` is infinite. -/
lemma tendsto_card_atTop_atTop [Infinite α] :
    Tendsto (Finset.card (α := α)) atTop atTop := by
  rw [Tendsto, map_card_atTop]

/-- `Finset.card` tends to `pure (Fintype.card α)`, when `α` is finite. -/
lemma tendsto_card_atTop_pure_of_fintype [Fintype α] :
    Tendsto (Finset.card : Finset α → ℕ) atTop (pure (Fintype.card α)) := by
  rw [Tendsto, map_card_atTop_of_fintype]

/-- `Tendsto` along `atTop` for a function precomposed with `Finset.card` reduces to `Tendsto` along
`atTop` on `ℕ`, when `α` is infinite. -/
lemma tendsto_comp_card_atTop_iff [Infinite α] {f : ℕ → β} {l : Filter β} :
    Tendsto (fun s : Finset α ↦ f s.card) atTop l ↔ Tendsto f atTop l := by
  rw [← map_card_atTop (α := α), tendsto_map'_iff]
  rfl

/-- `Tendsto` along `atTop` for a function precomposed with `Finset.card` reduces to `Tendsto` along
`pure (Fintype.card α)`, when `α` is finite. -/
lemma tendsto_comp_card_atTop_iff_of_fintype [Fintype α] {f : ℕ → β} {l : Filter β} :
    Tendsto (fun s : Finset α ↦ f s.card) atTop l ↔ Tendsto f (pure (Fintype.card α)) l := by
  rw [← map_card_atTop_of_fintype, tendsto_map'_iff]
  rfl

end Card

end Filter

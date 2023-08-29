/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Filter.Bases
import Mathlib.Order.Filter.Ultrafilter
/-!
# Subsingleton filters

We say that a filter `l` is a *subsingleton* if there exists a subsingleton set `s ∈ l`.
Equivalently, `l` is either `⊥` or `pure a` for some `a`.
-/

open Set
variable {α β : Type*} {l : Filter α}

namespace Filter

/-- We say that a filter is a *subsingleton* if there exists a subsingleton set
that belongs to the filter. -/
protected def Subsingleton (l : Filter α) : Prop := ∃ s ∈ l, Set.Subsingleton s

theorem HasBasis.subsingleton_iff {ι : Sort*} {p : ι → Prop} {s : ι → Set α} (h : l.HasBasis p s) :
    l.Subsingleton ↔ ∃ i, p i ∧ (s i).Subsingleton :=
  h.exists_iff fun _ _ hsub h ↦ h.anti hsub

theorem Subsingleton.anti {l'} (hl : l.Subsingleton) (hl' : l' ≤ l) : l'.Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨s, hl' hsl, hs⟩

@[nontriviality]
theorem Subsingleton.of_subsingleton [Subsingleton α] : l.Subsingleton :=
  ⟨univ, univ_mem, subsingleton_univ⟩

theorem Subsingleton.map (hl : l.Subsingleton) (f : α → β) : (map f l).Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; ⟨f '' s, image_mem_map hsl, hs.image f⟩

theorem Subsingleton.prod (hl : l.Subsingleton) {l' : Filter β} (hl' : l'.Subsingleton) :
    (l ×ˢ l').Subsingleton :=
  let ⟨s, hsl, hs⟩ := hl; let ⟨t, htl', ht⟩ := hl'; ⟨s ×ˢ t, prod_mem_prod hsl htl', hs.prod ht⟩

@[simp]
theorem subsingleton_pure {a : α} : Filter.Subsingleton (pure a) :=
  ⟨{a}, rfl, subsingleton_singleton⟩

@[simp]
theorem subsingleton_bot : Filter.Subsingleton (⊥ : Filter α) :=
  ⟨∅, trivial, subsingleton_empty⟩

/-- A nontrivial subsingleton filter is equal to `pure a` for some `a`. -/
theorem Subsingleton.exists_eq_pure [l.NeBot] (hl : l.Subsingleton) : ∃ a, l = pure a := by
  rcases hl with ⟨s, hsl, hs⟩
  -- ⊢ ∃ a, l = pure a
  rcases exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨nonempty_of_mem hsl, hs⟩ with ⟨a, rfl⟩
  -- ⊢ ∃ a, l = pure a
  refine ⟨a, (NeBot.le_pure_iff ‹_›).1 ?_⟩
  -- ⊢ l ≤ pure a
  rwa [le_pure_iff]
  -- 🎉 no goals

/-- A filter is a subsingleton iff it is equal to `⊥` or to `pure a` for some `a`. -/
theorem subsingleton_iff_bot_or_pure : l.Subsingleton ↔ l = ⊥ ∨ ∃ a, l = pure a := by
  refine ⟨fun hl ↦ ?_, ?_⟩
  -- ⊢ l = ⊥ ∨ ∃ a, l = pure a
  · exact (eq_or_neBot l).imp_right (@Subsingleton.exists_eq_pure _ _ · hl)
    -- 🎉 no goals
  · rintro (rfl | ⟨a, rfl⟩) <;> simp
    -- ⊢ Filter.Subsingleton ⊥
                                -- 🎉 no goals
                                -- 🎉 no goals

/-- In a nonempty type, a filter is a subsingleton iff
it is less than or equal to a pure filter. -/
theorem subsingleton_iff_exists_le_pure [Nonempty α] : l.Subsingleton ↔ ∃ a, l ≤ pure a := by
  rcases eq_or_neBot l with rfl | hbot
  -- ⊢ Filter.Subsingleton ⊥ ↔ ∃ a, ⊥ ≤ pure a
  · simp
    -- 🎉 no goals
  · simp [subsingleton_iff_bot_or_pure, ← hbot.le_pure_iff, hbot.ne]
    -- 🎉 no goals

theorem subsingleton_iff_exists_singleton_mem [Nonempty α] : l.Subsingleton ↔ ∃ a, {a} ∈ l := by
  simp only [subsingleton_iff_exists_le_pure, le_pure_iff]
  -- 🎉 no goals

/-- A subsingleton filter on a nonempty type is less than or equal to `pure a` for some `a`. -/
alias ⟨Subsingleton.exists_le_pure, _⟩ := subsingleton_iff_exists_le_pure

/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.CountableInter

open Function Filter Set Topology TopologicalSpace

variable {α X : Type _} [TopologicalSpace X] [T0Space X]

namespace Filter

section SecondCountableTopology

variable [SecondCountableTopology X]

section NoFun

variable {l : Filter X} [CountableInterFilter l]

theorem exists_subsingleton_mem_of_forall_open (hl : ∀ U, IsOpen U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ s : Set X, s.Subsingleton ∧ s ∈ l := by
  refine ⟨⋂₀ (countableBasis X ∩ l.sets) ∩ ⋂ (U ∈ countableBasis X) (_ : Uᶜ ∈ l), Uᶜ, ?_, ?_⟩
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    refine ((isBasis_countableBasis X).inseparable_iff.2 fun U hU ↦ ?_).eq
    cases hl U (isOpen_of_mem_countableBasis hU) with
    | inl hUl => simp only [hx.1 U ⟨hU, hUl⟩, hy.1 U ⟨hU, hUl⟩]
    | inr hUl => simp only [hx.2 U hU hUl, hy.2 U hU hUl]
  · exact inter_mem
      ((countable_sInter_mem ((countable_countableBasis _).mono (inter_subset_left _ _))).2 fun _ ↦
        And.right) <|
      (countable_bInter_mem (countable_countableBasis _)).2 fun U hU ↦ iInter_mem.2 id

theorem exists_singleton_mem_of_forall_open [Nonempty X] (hl : ∀ U, IsOpen U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ x : X, {x} ∈ l := by
  rcases exists_subsingleton_mem_of_forall_open hl with ⟨s, hs, hsl⟩
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  · obtain rfl : l = ⊥ := empty_mem_iff_bot.1 hsl
    simp
  · exact ⟨x, hsl⟩

end NoFun

variable {f g : α → X} {l : Filter α} [CountableInterFilter l]

theorem EventuallyEq.of_forall_open_mem_iff
    (h : ∀ U : Set X, IsOpen U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) : f =ᶠ[l] g :=
  have H : ∀ U ∈ countableBasis X, ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U := fun U hU ↦
    h U (isOpen_of_mem_countableBasis hU)
  ((eventually_countable_ball <| countable_countableBasis _).2 H).mono fun _ ↦
    (isBasis_countableBasis X).eq_iff.mpr

theorem eventuallyEq_iff_forall_open_mem_iff :
    f =ᶠ[l] g ↔ ∀ U : Set X, IsOpen U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U :=
  ⟨fun h U _ ↦ h.mono fun x hx ↦ by rw [hx], .of_forall_open_mem_iff⟩

theorem eventuallyEq_iff_forall_open_preimage :
    f =ᶠ[l] g ↔ ∀ U : Set X, IsOpen U → f ⁻¹' U =ᶠ[l] g ⁻¹' U :=
  eventuallyEq_iff_forall_open_mem_iff.trans <| by simp only [eventuallyEq_set, mem_preimage]

alias eventuallyEq_iff_forall_open_preimage ↔ _ EventuallyEq.of_forall_open_preimage

theorem exists_eventuallyEq_const_of_forall_open [Nonempty X]
    (h : ∀ U, IsOpen U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a : X, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_forall_open (l := map f l) h

end SecondCountableTopology

section NoFun

variable {l : Filter X} [CountableInterFilter l] {s : Set X} [SecondCountableTopology s]

theorem exists_subsingleton_mem_of_mem_of_forall_open (hs : s ∈ l)
    (hl : ∀ U, IsOpen U → U ∈ l ∨ Uᶜ ∈ l) : ∃ t, t ⊆ s ∧ t.Subsingleton ∧ t ∈ l := by
  replace hl : ∀ U : Set s, IsOpen U → U ∈ comap (↑) l ∨ Uᶜ ∈ comap (↑) l
  · rintro _ ⟨U, hU, rfl⟩
    exact (hl U hU).imp preimage_mem_comap preimage_mem_comap
  rcases exists_subsingleton_mem_of_forall_open hl with ⟨t, ht, htl⟩
  refine ⟨(↑) '' t, Subtype.coe_image_subset _ _, ht.image _,
    (mem_comap_iff Subtype.val_injective ?_).1 htl⟩
  rwa [Subtype.range_val]

theorem exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_open (hs : s ∈ l) (hne : s.Nonempty)
    (hl : ∀ U, IsOpen U → U ∈ l ∨ Uᶜ ∈ l) : ∃ a ∈ s, {a} ∈ l := by
  rcases exists_subsingleton_mem_of_mem_of_forall_open hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha ↦ ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩

theorem exists_singleton_mem_of_mem_of_forall_open [Nonempty X] (hs : s ∈ l)
    (hl : ∀ U, IsOpen U → U ∈ l ∨ Uᶜ ∈ l) : ∃ a, {a} ∈ l := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have : ∀ a, {a} ∈ l := fun _ ↦ mem_of_superset hs (empty_subset _)
    simp [this]
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_open hs hne hl).imp fun _ ↦
      And.right

end NoFun

variable {l : Filter α} [CountableInterFilter l] {s : Set X} [SecondCountableTopology s]

theorem exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_open (hs : ∀ᶠ x in l, f x ∈ s)
    (hne : s.Nonempty) (h : ∀ U, IsOpen U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a ∈ s, f =ᶠ[l] const α a :=
  exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_open (l := map f l) hs hne h

theorem exists_eventuallyEq_const_of_eventually_mem_of_forall_open [Nonempty X]
    (hs : ∀ᶠ x in l, f x ∈ s) (h : ∀ U, IsOpen U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_mem_of_forall_open (l := map f l) hs h

/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Filter.Partial

#align_import topology.partial from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Partial functions and topological spaces

In this file we prove properties of `Filter.PTendsto` etc in topological spaces. We also introduce
`PContinuous`, a version of `Continuous` for partially defined functions.
-/


open Filter

open Topology

variable {α β : Type*} [TopologicalSpace α]

theorem rtendsto_nhds {r : Rel β α} {l : Filter β} {a : α} :
    RTendsto r l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → r.core s ∈ l :=
  all_mem_nhds_filter _ _ (fun _s _t => id) _
#align rtendsto_nhds rtendsto_nhds

theorem rtendsto'_nhds {r : Rel β α} {l : Filter β} {a : α} :
    RTendsto' r l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → r.preimage s ∈ l := by
  rw [rtendsto'_def]
  -- ⊢ (∀ (s : Set α), s ∈ 𝓝 a → Rel.preimage r s ∈ l) ↔ ∀ (s : Set α), IsOpen s →  …
  apply all_mem_nhds_filter
  -- ⊢ ∀ (s t : Set α), s ⊆ t → Rel.preimage r s ⊆ Rel.preimage r t
  apply Rel.preimage_mono
  -- 🎉 no goals
#align rtendsto'_nhds rtendsto'_nhds

theorem ptendsto_nhds {f : β →. α} {l : Filter β} {a : α} :
    PTendsto f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f.core s ∈ l :=
  rtendsto_nhds
#align ptendsto_nhds ptendsto_nhds

theorem ptendsto'_nhds {f : β →. α} {l : Filter β} {a : α} :
    PTendsto' f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f.preimage s ∈ l :=
  rtendsto'_nhds
#align ptendsto'_nhds ptendsto'_nhds

/-! ### Continuity and partial functions -/


variable [TopologicalSpace β]

/-- Continuity of a partial function -/
def PContinuous (f : α →. β) :=
  ∀ s, IsOpen s → IsOpen (f.preimage s)
#align pcontinuous PContinuous

theorem open_dom_of_pcontinuous {f : α →. β} (h : PContinuous f) : IsOpen f.Dom := by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ
  -- ⊢ IsOpen (PFun.preimage f Set.univ)
                             -- 🎉 no goals
#align open_dom_of_pcontinuous open_dom_of_pcontinuous

theorem pcontinuous_iff' {f : α →. β} :
    PContinuous f ↔ ∀ {x y} (h : y ∈ f x), PTendsto' f (𝓝 x) (𝓝 y) := by
  constructor
  -- ⊢ PContinuous f → ∀ {x : α} {y : β}, y ∈ f x → PTendsto' f (𝓝 x) (𝓝 y)
  · intro h x y h'
    -- ⊢ PTendsto' f (𝓝 x) (𝓝 y)
    simp only [ptendsto'_def, mem_nhds_iff]
    -- ⊢ ∀ (s : Set β), (∃ t, t ⊆ s ∧ IsOpen t ∧ y ∈ t) → ∃ t, t ⊆ PFun.preimage f s  …
    rintro s ⟨t, tsubs, opent, yt⟩
    -- ⊢ ∃ t, t ⊆ PFun.preimage f s ∧ IsOpen t ∧ x ∈ t
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
    -- 🎉 no goals
  intro hf s os
  -- ⊢ IsOpen (PFun.preimage f s)
  rw [isOpen_iff_nhds]
  -- ⊢ ∀ (a : α), a ∈ PFun.preimage f s → 𝓝 a ≤ 𝓟 (PFun.preimage f s)
  rintro x ⟨y, ys, fxy⟩ t
  -- ⊢ t ∈ 𝓟 (PFun.preimage f s) → t ∈ 𝓝 x
  rw [mem_principal]
  -- ⊢ PFun.preimage f s ⊆ t → t ∈ 𝓝 x
  intro (h : f.preimage s ⊆ t)
  -- ⊢ t ∈ 𝓝 x
  change t ∈ 𝓝 x
  -- ⊢ t ∈ 𝓝 x
  apply mem_of_superset _ h
  -- ⊢ PFun.preimage f s ∈ 𝓝 x
  have h' : ∀ s ∈ 𝓝 y, f.preimage s ∈ 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  show f.preimage s ∈ 𝓝 x
  -- ⊢ PFun.preimage f s ∈ 𝓝 x
  apply h'
  -- ⊢ s ∈ 𝓝 y
  rw [mem_nhds_iff]
  -- ⊢ ∃ t, t ⊆ s ∧ IsOpen t ∧ y ∈ t
  exact ⟨s, Set.Subset.refl _, os, ys⟩
  -- 🎉 no goals
#align pcontinuous_iff' pcontinuous_iff'

theorem continuousWithinAt_iff_ptendsto_res (f : α → β) {x : α} {s : Set α} :
    ContinuousWithinAt f s x ↔ PTendsto (PFun.res f s) (𝓝 x) (𝓝 (f x)) :=
  tendsto_iff_ptendsto _ _ _ _
#align continuous_within_at_iff_ptendsto_res continuousWithinAt_iff_ptendsto_res

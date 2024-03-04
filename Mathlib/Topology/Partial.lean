/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Order.Filter.Partial
import Mathlib.Topology.Basic

#align_import topology.partial from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Partial functions and topological spaces

In this file we prove properties of `Filter.PTendsto` etc in topological spaces. We also introduce
`PContinuous`, a version of `Continuous` for partially defined functions.
-/


open Filter

open Topology

variable {X Y : Type*} [TopologicalSpace X]

theorem rtendsto_nhds {r : Rel Y X} {l : Filter Y} {x : X} :
    RTendsto r l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → r.core s ∈ l :=
  all_mem_nhds_filter _ _ (fun _s _t => id) _
#align rtendsto_nhds rtendsto_nhds

theorem rtendsto'_nhds {r : Rel Y X} {l : Filter Y} {x : X} :
    RTendsto' r l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → r.preimage s ∈ l := by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply Rel.preimage_mono
#align rtendsto'_nhds rtendsto'_nhds

theorem ptendsto_nhds {f : Y →. X} {l : Filter Y} {x : X} :
    PTendsto f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f.core s ∈ l :=
  rtendsto_nhds
#align ptendsto_nhds ptendsto_nhds

theorem ptendsto'_nhds {f : Y →. X} {l : Filter Y} {x : X} :
    PTendsto' f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f.preimage s ∈ l :=
  rtendsto'_nhds
#align ptendsto'_nhds ptendsto'_nhds

/-! ### Continuity and partial functions -/


variable [TopologicalSpace Y]

/-- Continuity of a partial function -/
def PContinuous (f : X →. Y) :=
  ∀ s, IsOpen s → IsOpen (f.preimage s)
#align pcontinuous PContinuous

theorem open_dom_of_pcontinuous {f : X →. Y} (h : PContinuous f) : IsOpen f.Dom := by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ
#align open_dom_of_pcontinuous open_dom_of_pcontinuous

theorem pcontinuous_iff' {f : X →. Y} :
    PContinuous f ↔ ∀ {x y} (h : y ∈ f x), PTendsto' f (𝓝 x) (𝓝 y) := by
  constructor
  · intro h x y h'
    simp only [ptendsto'_def, mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  intro hf s os
  rw [isOpen_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s ⊆ t)
  change t ∈ 𝓝 x
  apply mem_of_superset _ h
  have h' : ∀ s ∈ 𝓝 y, f.preimage s ∈ 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  show f.preimage s ∈ 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩
#align pcontinuous_iff' pcontinuous_iff'

theorem continuousWithinAt_iff_ptendsto_res (f : X → Y) {x : X} {s : Set X} :
    ContinuousWithinAt f s x ↔ PTendsto (PFun.res f s) (𝓝 x) (𝓝 (f x)) :=
  tendsto_iff_ptendsto _ _ _ _
#align continuous_within_at_iff_ptendsto_res continuousWithinAt_iff_ptendsto_res

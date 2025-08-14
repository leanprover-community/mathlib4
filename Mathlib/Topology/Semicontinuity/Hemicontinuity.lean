/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.NhdsWithin

/-! # Hemicontinuity

This files provides basic facts about upper and lower hemicontinuity of correspondences
`f : α → Set β`.
-/

@[expose] public section

open scoped Topology
open Set Filter

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f : α → Set β} {s : Set α} {x : α}

lemma upperHemicontinuousWithinAt_iff_preimage_Iic :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁, hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    refine fun s t hst hs ↦ Filter.mem_of_superset hs ?_
    gcongr
    exact hst
  case h₁ =>
    intro s t hst hs
    filter_upwards [hs] with x hx
    exact Filter.mem_of_superset hx hst
  refine forall₂_congr fun u ⟨hu, hfu⟩ ↦ ?_
  simp [hu.mem_nhdsSet, eventually_iff, Iic]

lemma upperHemicontinuousAt_iff_preimage_Iic :
    UpperHemicontinuousAt f x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝 x := by
  simpa [upperHemicontinuousWithinAt_univ_iff] using
    upperHemicontinuousWithinAt_iff_preimage_Iic (s := univ)

lemma upperHemicontinuousOn_iff_preimage_Iic :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_preimage_Iic]

lemma upperHemicontinuous_iff_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ x, ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝 x := by
  simp [upperHemicontinuous_iff, upperHemicontinuousAt_iff_preimage_Iic]

/-- A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *upper inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) sends open sets
to open sets. -/
lemma upperHemicontinuous_iff_isOpen_preimage_Iic :
    UpperHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic u)) := by
  simp_rw [upperHemicontinuous_iff_preimage_Iic, isOpen_iff_mem_nhds (s := f ⁻¹' (Iic _))]
  conv =>
    enter [1, x]
    rw [hasBasis_nhdsSet (f x) |>.forall_iff <|
      fun s t hst hs ↦ Filter.mem_of_superset hs <| by gcongr; exact hst]
  simp [forall_swap (α := α)]

/-- A correspondence `f : α → Set β` is upper hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends closed sets to closed sets. -/
lemma upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl :
    UpperHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' (Iic uᶜ))ᶜ := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact upperHemicontinuous_iff_isOpen_preimage_Iic

lemma isClosedMap_iff_upperHemicontinuous {f : α → β} :
    IsClosedMap f ↔ UpperHemicontinuous (f ⁻¹' {·}) := by
  rw [isClosedMap_iff_kernImage, upperHemicontinuous_iff_isOpen_preimage_Iic]
  aesop

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *lower inverse*
(i.e., `u : Set β ↦ (f ⁻¹' (Iic uᶜ))ᶜ`, note that `f ⁻¹' (Iic u) = {x | (f x ∩ u).Nonempty}`)
sends open sets to open sets. -/
lemma lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl :
    LowerHemicontinuous f ↔ ∀ u, IsOpen u → IsOpen (f ⁻¹' (Iic uᶜ))ᶜ := by
  have (u : Set β) : (f ⁻¹' (Iic uᶜ))ᶜ = {x | (f x ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff, this, isOpen_iff_mem_nhds,
    forall_swap (α := α), mem_setOf, Filter.Eventually]

/-- A correspondence `f : α → Set β` is lower hemicontinuous if and only if its *upper inverse*
(i.e., `u : Set β ↦ f ⁻¹' (Iic u)`, note that `f ⁻¹' (Iic u) = {x | f x ⊆ u}`) sends closed sets
to closed sets. -/
lemma lowerHemicontinuous_iff_isClosed_preimage_Iic :
    LowerHemicontinuous f ↔ ∀ u, IsClosed u → IsClosed (f ⁻¹' (Iic u)) := by
  conv_rhs =>
    rw [compl_surjective.forall]
    simp [← isOpen_compl_iff]
  exact lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl

lemma isOpenMap_iff_lowerHemicontinuous {f : α → β} :
    IsOpenMap f ↔ LowerHemicontinuous (f ⁻¹' {·}) := by
  rw [isOpenMap_iff_kernImage, lowerHemicontinuous_iff_isClosed_preimage_Iic]
  aesop

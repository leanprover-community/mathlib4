/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Completions of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.completion_iff`: a hausdorff completion has a nonarchimedean uniformity
  iff the underlying space has a nonarchimedean uniformity.

-/

variable {X Y : Type*}

open Filter Set Topology Uniformity

lemma IsUltraUniformity.of_isUniformInducing {Y : Type*} [UniformSpace X] [UniformSpace Y]
    [h : IsUltraUniformity Y] {f : X → Y} (hf : IsUniformInducing f) :
    IsUltraUniformity X := by
  apply mk_of_hasBasis (hf.basis_uniformity h.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ ↦ hU.preimage_prodMap f
  · exact fun _ ⟨_, _, hU⟩ ↦ hU.preimage_prodMap f

lemma IsSymmetricRel.cauchyFilter_gen [UniformSpace X] {s : Set (X × X)} (h : IsSymmetricRel s) :
    IsSymmetricRel (CauchyFilter.gen s) := by
  simp [IsSymmetricRel, CauchyFilter.gen, h.mem_filter_prod_comm]

lemma IsTransitiveRel.cauchyFilter_gen [UniformSpace X] {s : Set (X × X)} (hs : IsTransitiveRel s) :
    IsTransitiveRel (CauchyFilter.gen s) := by
  simp only [IsTransitiveRel, CauchyFilter.gen, mem_setOf_eq]
  intro f g h hfg hgh
  exact hs.mem_filter_prod_comm hfg hgh g.2.1

instance IsUltraUniformity.cauchyFilter [UniformSpace X]
    [h : IsUltraUniformity X] :
    IsUltraUniformity (CauchyFilter X) := by
  apply mk_of_hasBasis (CauchyFilter.basis_uniformity h.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ ↦ hU.cauchyFilter_gen
  · exact fun _ ⟨_, _, hU⟩ ↦ hU.cauchyFilter_gen

lemma IsUltraUniformity.cauchyFilter_iff [UniformSpace X] :
    IsUltraUniformity (CauchyFilter X) ↔ IsUltraUniformity X :=
  ⟨fun h ↦ h.of_isUniformInducing CauchyFilter.isUniformInducing_pureCauchy,
   fun _ ↦ inferInstance⟩

instance IsUltraUniformity.separationQuotient [UniformSpace X]
    [h : IsUltraUniformity X] :
    IsUltraUniformity (SeparationQuotient X) := by
  have := h.hasBasis.map (Prod.map SeparationQuotient.mk SeparationQuotient.mk)
  rw [← SeparationQuotient.uniformity_eq] at this
  apply mk_of_hasBasis this
  · exact fun _ ⟨_, hU, _⟩ ↦ hU.image_prodMap _
  · refine fun U ⟨hU', _, hU⟩ ↦ ?_
    rintro x y z
    simp only [id_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq,
      forall_exists_index, and_imp]
    rintro a b hab rfl rfl c d hcd hc rfl
    have hbc : (b, c) ∈ U := by
      rw [eq_comm, SeparationQuotient.mk_eq_mk, inseparable_iff_ker_uniformity,
          Filter.mem_ker] at hc
      exact hc _ hU'
    exact ⟨a, d, hU (hU hab hbc) hcd, by simp, by simp⟩

lemma IsUltraUniformity.separationQuotient_iff [UniformSpace X] :
    IsUltraUniformity (SeparationQuotient X) ↔ IsUltraUniformity X :=
  ⟨fun h ↦ h.of_isUniformInducing SeparationQuotient.isUniformInducing_mk,
   fun _ ↦ inferInstance⟩

lemma IsUltraUniformity.completion_iff [UniformSpace X] :
    IsUltraUniformity (UniformSpace.Completion X) ↔ IsUltraUniformity X := by
  rw [iff_comm, ← cauchyFilter_iff, ← separationQuotient_iff]
  exact Iff.rfl

instance IsUltraUniformity.completion [UniformSpace X]
    [h : IsUltraUniformity X] :
    IsUltraUniformity (UniformSpace.Completion X) :=
  completion_iff.2 h

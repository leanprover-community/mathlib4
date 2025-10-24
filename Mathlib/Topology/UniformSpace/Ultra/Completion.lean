/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.Ultra.Basic
import Mathlib.Topology.UniformSpace.Ultra.Constructions

/-!
# Completions of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.completion_iff`: a Hausdorff completion has a nonarchimedean uniformity
  iff the underlying space has a nonarchimedean uniformity.

-/

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y]

open Filter Set Topology Uniformity

lemma IsUniformInducing.isUltraUniformity [IsUltraUniformity Y] {f : X → Y}
    (hf : IsUniformInducing f) : IsUltraUniformity X :=
  hf.comap_uniformSpace ▸ .comap inferInstance f

instance CauchyFilter.isSymm_gen {s : SetRel X X} [s.IsSymm] : (gen s).IsSymm where
  symm _ := by simp [CauchyFilter.gen, s.mem_filter_prod_comm]


@[deprecated (since := "2025-10-17")]
alias IsSymmetricRel.cauchyFilter_gen := CauchyFilter.isSymm_gen

instance CauchyFilter.isTrans_gen {s : SetRel X X} [s.IsTrans] : (gen s).IsTrans where
  trans _ _ _ := IsTransitiveRel.mem_filter_prod_trans

@[deprecated (since := "2025-10-17")]
alias IsTransitiveRel.cauchyFilter_gen := CauchyFilter.isTrans_gen

instance IsUltraUniformity.cauchyFilter [IsUltraUniformity X] :
    IsUltraUniformity (CauchyFilter X) := by
  apply mk_of_hasBasis (CauchyFilter.basis_uniformity IsUltraUniformity.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ ↦ by simp; infer_instance
  · exact fun _ ⟨_, _, hU⟩ ↦ by simp; infer_instance

@[simp] lemma IsUltraUniformity.cauchyFilter_iff :
    IsUltraUniformity (CauchyFilter X) ↔ IsUltraUniformity X :=
  ⟨fun _ ↦ CauchyFilter.isUniformInducing_pureCauchy.isUltraUniformity,
   fun _ ↦ inferInstance⟩

instance IsUltraUniformity.separationQuotient [IsUltraUniformity X] :
    IsUltraUniformity (SeparationQuotient X) := by
  have := IsUltraUniformity.hasBasis.map
    (Prod.map SeparationQuotient.mk (SeparationQuotient.mk (X := X)))
  rw [← SeparationQuotient.uniformity_eq] at this
  apply mk_of_hasBasis this
  · exact fun _ ⟨_, hU, _⟩ ↦ by simp; infer_instance
  · rintro U ⟨hU', _, hU⟩
    constructor
    rintro x y z
    simp only [id_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq,
      forall_exists_index, and_imp]
    rintro a b hab rfl rfl c d hcd hc rfl
    have hbc : (b, c) ∈ U := by
      rw [eq_comm, SeparationQuotient.mk_eq_mk, inseparable_iff_ker_uniformity,
          Filter.mem_ker] at hc
      exact hc _ hU'
    exact ⟨a, d, U.trans (U.trans hab hbc) hcd, by simp, by simp⟩

@[simp] lemma IsUltraUniformity.separationQuotient_iff :
    IsUltraUniformity (SeparationQuotient X) ↔ IsUltraUniformity X :=
  ⟨fun _ ↦ SeparationQuotient.isUniformInducing_mk.isUltraUniformity,
   fun _ ↦ inferInstance⟩

@[simp] lemma IsUltraUniformity.completion_iff :
    IsUltraUniformity (UniformSpace.Completion X) ↔ IsUltraUniformity X := by
  rw [iff_comm, ← cauchyFilter_iff, ← separationQuotient_iff]
  exact Iff.rfl

instance IsUltraUniformity.completion [IsUltraUniformity X] :
    IsUltraUniformity (UniformSpace.Completion X) :=
  completion_iff.2 inferInstance

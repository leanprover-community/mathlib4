/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Setoid.Basic
/-!
# Bourbaki Strict Maps

This file defines Bourbaki strict maps and proves some of their basic properties.
A map `f` is strict if the quotient map to its image is a quotient map.
-/

@[expose] public section

open Function Set Topology


namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/-- Bourbaki strict map: quotient topology on the image. -/
def IsStrictMap : Prop :=
  IsQuotientMap (Set.rangeFactorization f)


lemma isHomeomorph_iff_isQuotientMap_injective {f : X → Y} :
    IsHomeomorph f ↔ IsQuotientMap f ∧ Injective f := by
  refine ⟨fun h ↦ ⟨h.isQuotientMap, h.injective⟩,
    fun h ↦ ⟨h.1.continuous, fun s hs ↦ ?_, h.2, h.1.surjective⟩⟩
  rwa [← h.1.isOpen_preimage, Set.preimage_image_eq _ h.2]

variable {f}

theorem isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔
      IsHomeomorph (Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) → Set.range f) := by
  simp only [IsStrictMap, isHomeomorph_iff_isQuotientMap_injective, Equiv.injective, and_true]
  exact ⟨fun h => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h,
         fun h ↦ h.comp isQuotientMap_quotient_mk'⟩

theorem isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (Setoid.kerLift f) := by
  simp only [isStrictMap_iff_quotientKerEquivRange_isHomeomorph,
    isHomeomorph_iff_isEmbedding_surjective, Equiv.surjective, and_true]
  exact (IsEmbedding.of_comp_iff .subtypeVal).symm

end Topology

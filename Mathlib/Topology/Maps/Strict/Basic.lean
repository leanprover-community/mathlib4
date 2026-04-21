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

This file defines Bourbaki strict maps (`Topology.IsStrictMap`) and proves some of their
basic properties. ?

A map `f : X → Y` between topological spaces is called *strict* in the sense of Bourbaki
if the natural corestriction to its image (i.e., `Set.rangeFactorization f`) is a quotient map.
Equivalently, these are precisely the maps for which the first isomorphism
theorem yields a homeomorphism: the canonical bijection `X ⧸ ker f ≃ range f`
is a homeomorphism if and only if `f` is strict. This provides a natural
generalization of quotient maps to non-surjective maps.

Many important classes of maps are automatically continuous strict maps, including:
- continuous open maps (`IsOpenMap.isStrictMap`);
- continuous closed maps (`IsClosedMap.isStrictMap`).

## Equivalent characterizations

We provide several equivalent ways to characterize a strict map `f`:
* `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange`: `f` is strict if and only if
  the canonical bijection `Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism.
* `Topology.isStrictMap_iff_isEmbedding_kerLift`: `f` is strict if and only if
  the canonical injection `Quotient (Setoid.ker f) → Y` (`Setoid.kerLift f`) is an embedding.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Function Set Topology

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/-- A map is a strict map in the sense of Bourbaki if the natural map to its image
is a quotient map. -/
def IsStrictMap : Prop :=
  IsQuotientMap (Set.rangeFactorization f)

lemma isStrictMap_iff_isQuotientMap_rangeFactorization :
    IsStrictMap f ↔ IsQuotientMap (Set.rangeFactorization f) :=
  Iff.rfl

variable {f}

/-- A map is a strict map if and only if the canonical bijection
`Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism. -/
theorem isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔
      IsHomeomorph (Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) → Set.range f) := by
  simp only [IsStrictMap, isHomeomorph_iff_isQuotientMap_injective, Equiv.injective, and_true]
  exact ⟨fun h => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h,
         fun h ↦ h.comp isQuotientMap_quotient_mk'⟩

/-- The homeomorphism `Quotient (Setoid.ker f) ≃ₜ Set.range f` given by a strict map `f`.
This is the homeomorphism obtained from the first isomorphism theorem. -/
noncomputable def Homeomorph.quotientKerEquivRange (hf : IsStrictMap f) :
    Quotient (Setoid.ker f) ≃ₜ Set.range f :=
  (isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

/-- A map is a strict map if and only if the canonical injection `Quotient (Setoid.ker f) → Y`
(`Setoid.kerLift f`) is an embedding. -/
theorem isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (Setoid.kerLift f) := by
  simp only [isStrictMap_iff_isHomeomorph_quotientKerEquivRange,
    isHomeomorph_iff_isEmbedding_surjective, Equiv.surjective, and_true]
  exact (IsEmbedding.of_comp_iff .subtypeVal).symm

/-- A strict map is continuous, since the range factorization is continuous. -/
lemma IsStrictMap.continuous {f : X → Y} (hf : IsStrictMap f) : Continuous f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at hf
  exact continuous_rangeFactorization_iff.mp hf.continuous

/-- A open continuous map is a strict map. -/
lemma IsOpenMap.isStrictMap (ho : IsOpenMap f) (h_cont : Continuous f) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (ho.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

/-- A closed continuous map is a strict map. -/
lemma IsClosedMap.isStrictMap (hc : IsClosedMap f) (h_cont : Continuous f) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (hc.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective


end Topology

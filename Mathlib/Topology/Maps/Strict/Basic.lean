/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Setoid.Basic
/-!
# Bourbaki Strict Maps

This file defines Bourbaki strict maps (`Topology.IsStrictMap`) and proves some of their
basic properties.

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

@[expose] public section

open Function Set Topology Setoid

namespace Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : X → Y) {g : Y → Z}

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

lemma IsHomeomorph.isStrictMap (f_homeo : IsHomeomorph f) :
    IsStrictMap f :=
  f_homeo.isOpenMap.isStrictMap f_homeo.continuous

lemma IsStrictMap.id : IsStrictMap (id : X → X) := IsHomeomorph.id.isStrictMap

lemma IsQuotientMap.isStrictMap_iff (f_quot : IsQuotientMap f) :
    IsStrictMap g ↔ IsStrictMap (g ∘ f) := by
  set Φ : range (g ∘ f) ≃ₜ range g := .setCongr <| f_quot.surjective.range_comp g
  have key : rangeFactorization g ∘ f = Φ ∘ rangeFactorization (g ∘ f) := rfl
  simp_rw [isStrictMap_iff_isQuotientMap_rangeFactorization, ← f_quot.of_comp_iff, key]
  exact ⟨fun H ↦ by simpa using Φ.symm.isQuotientMap.comp H, fun H ↦ Φ.isQuotientMap.comp H⟩

lemma IsQuotientMap.isStrictMap (f_quot : IsQuotientMap f) :
    IsStrictMap f :=
  f_quot.isStrictMap_iff.mp .id

lemma IsEmbedding.isStrictMap_iff (g_emb : IsEmbedding g) :
    IsStrictMap f ↔ IsStrictMap (g ∘ f) := by
  set Φ : Quotient (Setoid.ker (g ∘ f)) ≃ₜ Quotient (Setoid.ker (f)) :=
    Homeomorph.Quotient.congrRight (fun _ _ ↦ by simp [g_emb.injective.eq_iff])
  have key : g ∘ kerLift f ∘ Φ = kerLift (g ∘ f) :=
    funext <| Quotient.ind fun _ ↦ rfl
  simp_rw [isStrictMap_iff_isEmbedding_kerLift, ← g_emb.of_comp_iff, ← key]
  exact ⟨fun H ↦ H.comp Φ.isEmbedding,
    fun H ↦ by simpa [comp_assoc] using H.comp Φ.symm.isEmbedding⟩

lemma IsEmbedding.isStrictMap (f_emb : IsEmbedding f) :
    IsStrictMap f :=
  f_emb.isStrictMap_iff.mp .id

lemma isQuotientMap_iff_isStrictMap_surjective :
    IsQuotientMap f ↔ IsStrictMap f ∧ Surjective f := by
  refine ⟨fun H ↦ ⟨H.isStrictMap, H.surjective⟩, fun ⟨f_strict, f_surj⟩ ↦ ?_⟩
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at f_strict
  set Φ : range f ≃ₜ Y := .trans (.setCongr f_surj.range_eq) (Homeomorph.Set.univ Y)
  exact Φ.isQuotientMap.comp f_strict

lemma isEmbedding_iff_isStrictMap_injective :
    IsEmbedding f ↔ IsStrictMap f ∧ Injective f := by
  refine ⟨fun H ↦ ⟨H.isStrictMap, H.injective⟩, fun ⟨f_strict, f_inj⟩ ↦ ?_⟩
  rw [isStrictMap_iff_isEmbedding_kerLift] at f_strict
  set Φ : Quotient (ker f) ≃ₜ X :=
    (Homeomorph.Quotient.congrRight <| by simp [f_inj.eq_iff]).trans Homeomorph.quotientBot
  exact f_strict.comp Φ.symm.isEmbedding

end Topology

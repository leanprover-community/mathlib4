/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
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

* `Topology.IsStrictMap`: The condition that a map `f` is strict, meaning the natural
  map to its image is a quotient map.

## Equivalent characterizations

We provide several equivalent ways to characterize a strict map `f`:
* `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange`: `f` is strict if and only if
  the canonical bijection `Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism.
* `Topology.isStrictMap_iff_isEmbedding_kerLift`: `f` is strict if and only if
  the canonical injection `Quotient (Setoid.ker f) → Y` (`Setoid.kerLift f`) is an embedding.

### Group homomorphisms

In general, the product (in the sense of `Prod.map`) of two strict maps need not be strict.
But thanks to `MonoidHom.isOpenQuotientMap_of_isQuotientMap`, we can replace `IsQuotientMap`
by `IsOpenQuotientMap` in the setting of group homomorphisms. Therefore we provide several
impotant properties of a strict group homomorphisms `f` :

* `isStrictMap_iff_isOpenQuotientMap_rangeRestrict`: `f` is a strict group homomorphism if
  and only if the `rangeRestrict` of `f` is an open quotient map.
* `isStrictMap_prodMap`: The product (in the sense of Prod.map) of group homomorphisms is strict
-/

@[expose] public section

open Function Set Topology


namespace Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y)

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

/-- Strict maps stay strict when we compose them with homeomorphisms -/
lemma Homeomorph.comp_isStrictMap (e : X ≃ₜ Y) {f : Y → Z} (hf : IsStrictMap f) :
    IsStrictMap (f ∘ e) :=
  by
    rw [IsStrictMap] at hf ⊢
    let erange : Set.range (f ∘ e) ≃ₜ Set.range f :=
      Homeomorph.setCongr (by simp [Set.range_comp])
    convert erange.symm.isQuotientMap.comp (hf.comp e.isQuotientMap) using 1

end Topology

namespace MonoidHom
open Topology

variable {G H G' H' : Type*} [Group G'] [Group H'] [Group G] [Group H]
variable (f : G →* H) (g : G' →* H')

/-- The range of a product of group homomorphisms is the product of their ranges. -/
lemma range_prodMap :
    (f.prodMap g).range = f.range.prod g.range := by
  ext ⟨h, h'⟩
  simp only [Subgroup.mem_prod, MonoidHom.mem_range, MonoidHom.coe_prodMap,
             Prod.map_apply, Prod.exists, Prod.mk.injEq]
  tauto

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]

/-- A quotient group homomorphism from a topological group is automatically an open quotient map. -/
lemma isQuotientMap_iff_isOpenQuotientMap :
    IsOpenQuotientMap f ↔ IsQuotientMap f := by
  exact ⟨fun hf => hf.isQuotientMap, MonoidHom.isOpenQuotientMap_of_isQuotientMap⟩

/-- A group homomorphism is strict if and only if its rangeRestrict is an open quotient map. -/
lemma isStrictMap_iff_isOpenQuotientMap_rangeRestrict :
    IsStrictMap f ↔ IsOpenQuotientMap f.rangeRestrict := by
  rw [isQuotientMap_iff_isOpenQuotientMap]
  rfl

variable [TopologicalSpace G'] [IsTopologicalGroup G'] [TopologicalSpace H']

noncomputable def rangeProdMapHomeomorph :
    (f.prodMap g).range ≃ₜ f.range × g.range :=
  (Homeomorph.setCongr (by simp [range_prodMap, Subgroup.coe_prod])).trans
    (Homeomorph.Set.prod _ _)

/-- The product (in the sense of Prod.map) of group homomorphisms is strict -/
lemma isStrictMap_prodMap (hf : IsStrictMap f) (hg : IsStrictMap g) :
    IsStrictMap (f.prodMap g) := by
  rw [isStrictMap_iff_isOpenQuotientMap_rangeRestrict]
  have hf' := (isStrictMap_iff_isOpenQuotientMap_rangeRestrict (f := f)).mp hf
  have hg' := (isStrictMap_iff_isOpenQuotientMap_rangeRestrict (f := g)).mp hg
  convert (rangeProdMapHomeomorph (f := f) (g := g)).symm.isOpenQuotientMap.comp
    (hf'.prodMap hg') using 1

end MonoidHom

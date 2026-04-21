/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Baire.Lemmas

/-!
# Open quotient maps

An open quotient map is an open map `f : X → Y` which is both an open map and a quotient map.
Equivalently, it is a surjective continuous open map.
We use the latter characterization as a definition.

Many important quotient maps are open quotient maps, including

- the quotient map from a topological space to its quotient by the action of a group;
- the quotient map from a topological group to its quotient by a normal subgroup;
- the quotient map from a topological space to its separation quotient.

Contrary to general quotient maps,
the category of open quotient maps is closed under `Prod.map`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Filter Function Set Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}

namespace IsOpenQuotientMap

protected theorem id : IsOpenQuotientMap (id : X → X) := ⟨surjective_id, continuous_id, .id⟩

/-- An open quotient map is a quotient map. -/
theorem isQuotientMap (h : IsOpenQuotientMap f) : IsQuotientMap f :=
  h.isOpenMap.isQuotientMap h.continuous h.surjective

theorem iff_isOpenMap_isQuotientMap : IsOpenQuotientMap f ↔ IsOpenMap f ∧ IsQuotientMap f :=
  ⟨fun h ↦ ⟨h.isOpenMap, h.isQuotientMap⟩, fun ⟨ho, hq⟩ ↦ ⟨hq.surjective, hq.continuous, ho⟩⟩

theorem of_isOpenMap_isQuotientMap (ho : IsOpenMap f) (hq : IsQuotientMap f) :
    IsOpenQuotientMap f :=
  iff_isOpenMap_isQuotientMap.2 ⟨ho, hq⟩

theorem comp {g : Y → Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f) :
    IsOpenQuotientMap (g ∘ f) :=
  ⟨.comp hg.1 hf.1, .comp hg.2 hf.2, .comp hg.3 hf.3⟩

theorem map_nhds_eq (h : IsOpenQuotientMap f) (x : X) : map f (𝓝 x) = 𝓝 (f x) :=
  le_antisymm h.continuous.continuousAt <| h.isOpenMap.nhds_le _

theorem continuous_comp_iff (h : IsOpenQuotientMap f) {g : Y → Z} :
    Continuous (g ∘ f) ↔ Continuous g :=
  h.isQuotientMap.continuous_iff.symm

theorem continuousAt_comp_iff (h : IsOpenQuotientMap f) {g : Y → Z} {x : X} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  simp only [ContinuousAt, ← h.map_nhds_eq, tendsto_map'_iff, comp_def]

theorem dense_preimage_iff (h : IsOpenQuotientMap f) {s : Set Y} : Dense (f ⁻¹' s) ↔ Dense s :=
  ⟨fun hs ↦ h.surjective.denseRange.dense_of_mapsTo h.continuous hs (mapsTo_preimage _ _),
    fun hs ↦ hs.preimage h.isOpenMap⟩

/-- If `f` is an open quotient map and `X` is Baire, then `Y` is Baire. -/
theorem baireSpace {f : X → Y} [BaireSpace X] (hf : IsOpenQuotientMap f) :
    BaireSpace Y := by
  constructor
  intro u hou hdu
  have := dense_iInter_of_isOpen_nat (fun n => hf.continuous.isOpen_preimage (u n) (hou n))
    (fun n => (IsOpenQuotientMap.dense_preimage_iff hf).mpr (hdu n))
  simp_all [← preimage_iInter, IsOpenQuotientMap.dense_preimage_iff]

end IsOpenQuotientMap

theorem Topology.IsInducing.isOpenQuotientMap_of_surjective (ind : IsInducing f)
    (surj : Function.Surjective f) : IsOpenQuotientMap f where
  surjective := surj
  continuous := ind.continuous
  isOpenMap U U_open := by
    obtain ⟨V, hV, rfl⟩ := ind.isOpen_iff.mp U_open
    rwa [V.image_preimage_eq surj]

theorem Topology.IsInducing.isQuotientMap_of_surjective (ind : IsInducing f)
    (surj : Function.Surjective f) : IsQuotientMap f :=
  (ind.isOpenQuotientMap_of_surjective surj).isQuotientMap

section Subquotient

variable {A B C D : Type*}
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
variable (f : A → B) (g : C → D) (p : A → C) (q : B → D)

omit [TopologicalSpace C] in
/--
Given the following diagram with `f` inducing, `p` surjective,
`q` an open quotient map, and `g` injective. Suppose the image of `A` in `B` is stable
under the equivalence mod `q`, then the coinduced topology on `C` (from `A`)
coincides with the induced topology (from `D`).
```
A -f→ B
∣     ∣
p     q
↓     ↓
C -g→ D
```

A typical application is when `K ≤ H` are subgroups of `G`, then the quotient topology on `H/K`
is also the subspace topology from `G/K`.
-/
lemma coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : Function.Surjective p)
    (hq : IsOpenQuotientMap q) (hg : Function.Injective g)
    (H : q ⁻¹' (q '' (Set.range f)) ⊆ Set.range f) :
    ‹TopologicalSpace A›.coinduced p = ‹TopologicalSpace D›.induced g := by
  ext U
  change IsOpen (p ⁻¹' U) ↔ ∃ V, _
  simp_rw [hf.isOpen_iff,
    (Set.image_surjective.mpr hq.surjective).exists,
    ← hq.isQuotientMap.isOpen_preimage]
  constructor
  · rintro ⟨V, hV, e⟩
    refine ⟨V, hq.continuous.1 _ (hq.isOpenMap _ hV), ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := hp x
    constructor
    · rintro ⟨y, hy, e'⟩
      obtain ⟨y, rfl⟩ := H ⟨_, ⟨x, rfl⟩, (e'.trans (congr_fun h x)).symm⟩
      rw [← hg ((congr_fun h y).trans e')]
      exact e.le hy
    · intro H
      exact ⟨f x, e.ge H, congr_fun h.symm x⟩
  · rintro ⟨V, hV, rfl⟩
    refine ⟨_, hV, ?_⟩
    simp_rw [← Set.preimage_comp, h]

lemma isEmbedding_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : IsQuotientMap p)
    (hq : IsOpenQuotientMap q) (hg : Function.Injective g)
    (H : q ⁻¹' (q '' (Set.range f)) ⊆ Set.range f) :
    IsEmbedding g :=
  ⟨⟨hp.eq_coinduced.trans (coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp.surjective hq hg H)⟩, hg⟩

lemma isQuotientMap_of_isOpenQuotientMap_of_isInducing
    (h : g ∘ p = q ∘ f)
    (hf : IsInducing f) (hp : Surjective p)
    (hq : IsOpenQuotientMap q) (hg : IsEmbedding g)
    (H : q ⁻¹' (q '' (Set.range f)) ⊆ Set.range f) :
    IsQuotientMap p :=
  ⟨⟨hg.eq_induced.trans ((coinduced_eq_induced_of_isOpenQuotientMap_of_isInducing
    f g p q h hf hp hq hg.injective H)).symm⟩, hp⟩

end Subquotient

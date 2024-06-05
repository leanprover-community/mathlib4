/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.FiberBundle.Basic

#align_import topology.covering from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `Trivialization` of `f` at `x` with fiber `I`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/


open Bundle

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet
#align is_evenly_covered IsEvenlyCovered

namespace IsEvenlyCovered

variable {f}

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm
#align is_evenly_covered.to_trivialization IsEvenlyCovered.toTrivialization

theorem mem_toTrivialization_baseSet {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : x ∈ h.toTrivialization.baseSet :=
  Classical.choose_spec h.2
#align is_evenly_covered.mem_to_trivialization_base_set IsEvenlyCovered.mem_toTrivialization_baseSet

theorem toTrivialization_apply {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toPartialEquiv.eq_symm_apply (e.mem_source.mpr h)
            (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm
#align is_evenly_covered.to_trivialization_apply IsEvenlyCovered.toTrivialization_apply

protected theorem continuousAt {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
#align is_evenly_covered.continuous_at IsEvenlyCovered.continuousAt

theorem to_isEvenlyCovered_preimage {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨_, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph
          (Classical.choose_spec h2)).embedding.discreteTopology,
    _, h.mem_toTrivialization_baseSet⟩
#align is_evenly_covered.to_is_evenly_covered_preimage IsEvenlyCovered.to_isEvenlyCovered_preimage

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map_on IsCoveringMapOn

namespace IsCoveringMapOn

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩
#align is_covering_map_on.mk IsCoveringMapOn.mk

variable {f} {s}

protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x :=
  (hf (f x) hx).continuousAt
#align is_covering_map_on.continuous_at IsCoveringMapOn.continuousAt

protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  ContinuousAt.continuousOn fun _ => hf.continuousAt
#align is_covering_map_on.continuous_on IsCoveringMapOn.continuousOn

protected theorem isLocalHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocalHomeomorphOn f (f ⁻¹' s) := by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx => ?_
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toPartialHomeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.baseSet ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.baseSet
          open_source :=
            e.open_baseSet.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_baseSet
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p _ => rfl
          continuousOn_toFun := continuous_fst.continuousOn
          continuousOn_invFun := (continuous_id'.prod_mk continuous_const).continuousOn },
      ⟨he, by rwa [e.toPartialHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩
#align is_covering_map_on.is_locally_homeomorph_on IsCoveringMapOn.isLocalHomeomorphOn

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map IsCoveringMap

variable {f}

theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]
#align is_covering_map_iff_is_covering_map_on_univ isCoveringMap_iff_isCoveringMapOn_univ

protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf
#align is_covering_map.is_covering_map_on IsCoveringMap.isCoveringMapOn

variable (f)

namespace IsCoveringMap

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (IsCoveringMapOn.mk f Set.univ F (fun x _ => e x) fun x _ => h x)
#align is_covering_map.mk IsCoveringMap.mk

variable {f} (hf : IsCoveringMap f)

protected theorem continuous : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.isCoveringMapOn.continuousOn
#align is_covering_map.continuous IsCoveringMap.continuous

protected theorem isLocalHomeomorph : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn
#align is_covering_map.is_locally_homeomorph IsCoveringMap.isLocalHomeomorph

protected theorem isOpenMap : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap
#align is_covering_map.is_open_map IsCoveringMap.isOpenMap

protected theorem quotientMap (hf' : Function.Surjective f) : QuotientMap f :=
  hf.isOpenMap.to_quotientMap hf.continuous hf'
#align is_covering_map.quotient_map IsCoveringMap.quotientMap

protected theorem isSeparatedMap : IsSeparatedMap f :=
  fun e₁ e₂ he hne ↦ by
    obtain ⟨_, t, he₁⟩ := hf (f e₁)
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine ⟨t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₁).2}, t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₂).2},
      ?_, ?_, ⟨he₁, rfl⟩, ⟨he₂, rfl⟩, Set.disjoint_left.mpr fun x h₁ h₂ ↦ hne (t.injOn he₁ he₂ ?_)⟩
    iterate 2
      exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
        (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
    refine Prod.ext ?_ (h₁.2.symm.trans h₂.2)
    rwa [t.proj_toFun e₁ he₁, t.proj_toFun e₂ he₂]

variable {A} [TopologicalSpace A] {s : Set A} (hs : IsPreconnected s) {g g₁ g₂ : A → E}

theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

theorem eqOn_of_comp_eqOn (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ :=
  hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', f (g a) = f (g a')) (a a') : g a = g a' :=
  hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

theorem constOn_of_comp (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, f (g a) = f (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

end IsCoveringMap

variable {f}

protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
#align is_fiber_bundle.is_covering_map IsFiberBundle.isCoveringMap

protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩
#align fiber_bundle.is_covering_map FiberBundle.isCoveringMap

/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a homeomorphism `f ⁻¹' U ≃ₜ U × I` for some open set `U` containing `x`
  with `f ⁻¹' U` open, such that the induced map `f ⁻¹' U → U` coincides with `f`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/

@[expose] public section

open Bundle Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood.

**Remark**: `DiscreteTopology I ∧ ∃ Trivialization I f, x ∈ t.baseSet` would be a simpler
definition, but unfortunately it does not work if `E` is nonempty but nonetheless `f` has empty
fibers over `s`. If `OpenPartialHomeomorph` could be refactored to work with an empty space and a
nonempty space while preserving the APIs, we could switch back to the definition. -/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    ∃ H : f ⁻¹' U ≃ₜ U × I, ∀ x, (H x).1.1 = f x

namespace IsEvenlyCovered

variable {f} {I : Type*} [TopologicalSpace I]

/-- If `x : X` is evenly covered by `f` with fiber `I`, then `I` is homeomorphic to `f ⁻¹' {x}`. -/
noncomputable def fiberHomeomorph {x : X} (h : IsEvenlyCovered f x I) : I ≃ₜ f ⁻¹' {x} := by
  choose _ U hxU hU hfU H hH using h
  exact
  { toFun i := ⟨H.symm (⟨x, hxU⟩, i), by simp [← hH]⟩
    invFun e := (H ⟨e, by rwa [Set.mem_preimage, (e.2 : f e = x)]⟩).2
    left_inv _ := by simp
    right_inv e := Set.inclusion_injective (Set.preimage_mono (Set.singleton_subset_iff.mpr hxU)) <|
      H.injective <| Prod.ext (Subtype.ext <| by simpa [hH] using e.2.symm) (by simp)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

theorem discreteTopology_fiber {x : X} (h : IsEvenlyCovered f x I) : DiscreteTopology (f ⁻¹' {x}) :=
  have := h.1; h.fiberHomeomorph.discreteTopology

/-- If `x` is evenly covered by `f` with nonempty fiber `I`, then we can construct a
trivialization of `f` at `x` with fiber `I`. -/
noncomputable def toTrivialization' {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization I f := by
  choose _ U hxU hU hfU H hH using h
  classical exact
  { toFun e := if he : f e ∈ U then ⟨(H ⟨e, he⟩).1, (H ⟨e, he⟩).2⟩ else ⟨x, Classical.arbitrary I⟩
    invFun xi := H.symm (if hx : xi.1 ∈ U then ⟨xi.1, hx⟩ else ⟨x, hxU⟩, xi.2)
    source := f ⁻¹' U
    target := U ×ˢ Set.univ
    map_source' e (he : f e ∈ U) := by simp [he]
    map_target' _ _ := Subtype.coe_prop _
    left_inv' e (he : f e ∈ U) := by simp [he]
    right_inv' xi := by rintro ⟨hx, -⟩; simpa [hx] using fun h ↦ (h (H.symm _).2).elim
    open_source := hfU
    open_target := hU.prod isOpen_univ
    continuousOn_toFun := continuousOn_iff_continuous_restrict.mpr <|
      ((continuous_subtype_val.prodMap continuous_id).comp H.continuous).congr
      fun ⟨e, (he : f e ∈ U)⟩ ↦ by simp [Prod.map, he]
    continuousOn_invFun := continuousOn_iff_continuous_restrict.mpr <|
      ((continuous_subtype_val.comp H.symm.continuous).comp (by fun_prop :
        Continuous fun ui ↦ ⟨⟨_, ui.2.1⟩, ui.1.2⟩)).congr fun ⟨⟨x, i⟩, ⟨hx, _⟩⟩ ↦ by simp [hx]
    baseSet := U
    open_baseSet := hU
    source_eq := rfl
    target_eq := rfl
    proj_toFun e (he : f e ∈ U) := by simp [he, hH] }

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization (f ⁻¹' {x}) f :=
  h.toTrivialization'.transFiberHomeomorph h.fiberHomeomorph

theorem mem_toTrivialization_baseSet {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    x ∈ h.toTrivialization.baseSet := h.2.choose_spec.1

theorem toTrivialization_apply {x : E} [Nonempty I] (h : IsEvenlyCovered f (f x) I) :
    (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  h.fiberHomeomorph.symm.injective <| by
    simp [toTrivialization, toTrivialization', dif_pos h.2.choose_spec.1, fiberHomeomorph]

protected theorem continuousAt {x : E} (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  have ⟨_, _, hxU, _, _, H, _⟩ := h
  have : Nonempty I := ⟨(H ⟨x, hxU⟩).2⟩
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))

theorem of_fiber_homeomorph {J} [TopologicalSpace J] (g : I ≃ₜ J) {x : X}
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x J :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨g.discreteTopology, U, hxU, hU, hfU, H.trans (.prodCongr (.refl U) g), fun _ ↦ by simp [hH]⟩

theorem to_isEvenlyCovered_preimage {x : X} (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  h.of_fiber_homeomorph h.fiberHomeomorph

theorem of_trivialization [DiscreteTopology I] {x : X} {t : Trivialization I f}
    (hx : x ∈ t.baseSet) : IsEvenlyCovered f x I :=
  ⟨‹_›, _, hx, t.open_baseSet, t.source_eq ▸ t.open_source,
  { toFun e := ⟨⟨f e, e.2⟩, (t e).2⟩
    invFun xi := ⟨t.invFun (xi.1, xi.2), by
      rw [Set.mem_preimage, ← t.mem_source]; exact t.map_target (t.target_eq ▸ ⟨xi.1.2, ⟨⟩⟩)⟩
    left_inv e := Subtype.ext <| t.symm_apply_mk_proj (t.mem_source.mpr e.2)
    right_inv xi := by simp [t.proj_symm_apply', t.apply_symm_apply']
    continuous_toFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuous_iff.mpr <|
      (continuousOn_iff_continuous_restrict.mp <| t.continuousOn_toFun.mono t.source_eq.ge).congr
      fun e ↦ by simp [t.mk_proj_snd' e.2]
    continuous_invFun := Topology.IsInducing.subtypeVal.continuous_iff.mpr <|
      t.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun ⟨x, _⟩ ↦ t.target_eq ▸ ⟨x.2, ⟨⟩⟩ }, fun _ ↦ by simp⟩

variable (I) in
theorem of_preimage_eq_empty [IsEmpty I] {x : X} {U : Set X} (hUx : U ∈ 𝓝 x) (hfU : f ⁻¹' U = ∅) :
    IsEvenlyCovered f x I :=
  have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})

namespace IsCoveringMapOn

theorem of_isEmpty [IsEmpty E] : IsCoveringMapOn f s := fun _ _ ↦ .to_isEvenlyCovered_preimage
  (.of_preimage_eq_empty Empty Filter.univ_mem <| Set.eq_empty_of_isEmpty _)

/-- A constructor for `IsCoveringMapOn` when there are both empty and nonempty fibers. -/
theorem mk' (F : s → Type*) [∀ x : s, TopologicalSpace (F x)] [hF : ∀ x : s, DiscreteTopology (F x)]
    (t : ∀ x : s, x.1 ∈ Set.range f → {t : Trivialization (F x) f // x.1 ∈ t.baseSet})
    (h : ∀ x : s, x.1 ∉ Set.range f → ∃ U ∈ 𝓝 x.1, f ⁻¹' U = ∅) :
    IsCoveringMapOn f s := fun x hx ↦ by
  lift x to s using hx
  by_cases hxf : x.1 ∈ Set.range f
  · exact .to_isEvenlyCovered_preimage (.of_trivialization (t x hxf).2)
  · have ⟨U, hUx, hfU⟩ := h x hxf
    exact .to_isEvenlyCovered_preimage (.of_preimage_eq_empty Empty hUx hfU)

theorem mk (F : s → Type*) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x.1 ∈ (e x).baseSet) :
    IsCoveringMapOn f s := by
  cases isEmpty_or_nonempty E
  · exact .of_isEmpty _ _
  refine .mk' _ _ _ (fun x _ ↦ ⟨e x, h x⟩) fun x hx ↦ (hx ?_).elim
  exact ⟨(e x).invFun (x, (e x <| Classical.arbitrary E).2), (e x).proj_symm_apply' (h x)⟩

variable {f s}

protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x := (hf (f x) hx).continuousAt

protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  continuousOn_of_forall_continuousAt fun _ ↦ hf.continuousAt

protected theorem isLocalHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocalHomeomorphOn f (f ⁻¹' s) := by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx ↦ ?_
  have : Nonempty (f ⁻¹' {f x}) := ⟨⟨x, rfl⟩⟩
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toOpenPartialHomeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.baseSet ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.baseSet
          open_source :=
            e.open_baseSet.prod (discreteTopology_iff_isOpen_singleton.1 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_baseSet
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p _ => rfl
          continuousOn_toFun := continuousOn_fst
          continuousOn_invFun := by fun_prop },
      ⟨he, by rwa [e.toOpenPartialHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})

variable {f}

theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf

variable (f)

namespace IsCoveringMap

theorem of_isEmpty [IsEmpty E] : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| .of_isEmpty _ _

theorem of_discreteTopology [DiscreteTopology E] [DiscreteTopology X] : IsCoveringMap f :=
  fun x ↦ ⟨inferInstance, {x}, rfl, isOpen_discrete _, isOpen_discrete _,
    { toFun e := ⟨⟨x, rfl⟩, e⟩
      invFun xi := xi.2
      left_inv _ := rfl
      right_inv _ := Prod.ext (Subsingleton.elim ..) rfl },
    (·.2.symm)⟩

/-- A constructor for `IsCoveringMap` when there are both empty and nonempty fibers. -/
theorem mk' (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (t : ∀ x, x ∈ Set.range f → {t : Trivialization (F x) f // x ∈ t.baseSet})
    (h : IsClosed (Set.range f)) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| .mk' f _ _ (fun x h ↦ t x h) fun _x hx ↦
    ⟨_, h.isOpen_compl.mem_nhds hx, Set.eq_empty_of_forall_notMem fun x h ↦ h ⟨x, rfl⟩⟩

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| .mk _ _ _ _ fun x ↦ h x

variable {f}
variable (hf : IsCoveringMap f)
include hf

protected theorem continuous : Continuous f :=
  continuousOn_univ.mp hf.isCoveringMapOn.continuousOn

protected theorem isLocalHomeomorph : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn

protected theorem isOpenMap : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap

theorem isQuotientMap (hf' : Function.Surjective f) : IsQuotientMap f :=
  hf.isOpenMap.isQuotientMap hf.continuous hf'

protected theorem isSeparatedMap : IsSeparatedMap f :=
  fun e₁ e₂ he hne ↦ by
    have : Nonempty (f ⁻¹' {f e₁}) := ⟨⟨e₁, rfl⟩⟩
    specialize hf (f e₁)
    let t := hf.toTrivialization
    have := hf.discreteTopology_fiber
    have he₁ := hf.mem_toTrivialization_baseSet
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine ⟨t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₁).2}, t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₂).2},
      ?_, ?_, ⟨he₁, rfl⟩, ⟨he₂, rfl⟩, Set.disjoint_left.mpr fun x h₁ h₂ ↦ hne (t.injOn he₁ he₂ ?_)⟩
    iterate 2
      exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
        (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
    refine Prod.ext ?_ (h₁.2.symm.trans h₂.2)
    rwa [t.proj_toFun e₁ he₁, t.proj_toFun e₂ he₂]

variable {A} [TopologicalSpace A] {s : Set A} {g g₁ g₂ : A → E} {γ γ₁ γ₂ : C(A, E)}

/-- Proposition 1.34 of [hatcher02]. -/
theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

theorem eq_of_comp_eq_CM [PreconnectedSpace A] (h : f ∘ γ₁ = f ∘ γ₂) (a : A) (ha : γ₁ a = γ₂ a) :
    γ₁ = γ₂ :=
  DFunLike.coe_injective <| hf.eq_of_comp_eq γ₁.continuous γ₂.continuous h a ha

theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', f (g a) = f (g a')) (a a') : g a = g a' :=
  hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

theorem const_of_comp_CM [PreconnectedSpace A] (he : ∀ a a', f (γ a) = f (γ a')) (a a') :
    γ a = γ a' :=
  const_of_comp hf γ.continuous he _ _

theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ :=
  hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, f (g a) = f (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

end IsCoveringMap

variable {f}

protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)

protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩

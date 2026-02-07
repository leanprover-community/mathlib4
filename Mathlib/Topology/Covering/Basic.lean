/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.IsLocalHomeomorph

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
    continuous_toFun := (IsInducing.subtypeVal.prodMap .id).continuous_iff.mpr <|
      (continuousOn_iff_continuous_restrict.mp <| t.continuousOn_toFun.mono t.source_eq.ge).congr
      fun e ↦ by simp [t.mk_proj_snd' e.2]
    continuous_invFun := IsInducing.subtypeVal.continuous_iff.mpr <|
      t.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun ⟨x, _⟩ ↦ t.target_eq ▸ ⟨x.2, ⟨⟩⟩ }, fun _ ↦ by simp⟩

variable (I) in
theorem of_preimage_eq_empty [IsEmpty I] {x : X} {U : Set X} (hUx : U ∈ 𝓝 x) (hfU : f ⁻¹' U = ∅) :
    IsEvenlyCovered f x I :=
  have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩

theorem restrictPreimage {x : X} (hxs : x ∈ s) (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered (s.restrictPreimage f) ⟨x, hxs⟩ I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, Subtype.val ⁻¹' U, hxU, hU.preimage (by fun_prop), hfU.preimage continuous_subtype_val,
    { toFun e := (⟨⟨(H ⟨e, e.2⟩).1, hH _ ▸ e.1.2⟩, by simpa only [hH] using e.2⟩, (H ⟨e, e.2⟩).2)
      invFun x := ⟨⟨H.symm (⟨x.1, x.1.2⟩, x.2), by simp [← hH]⟩, by simp [← hH]⟩
      left_inv _ := by simp, right_inv _ := by simp }, fun _ ↦ by ext; apply hH⟩

theorem subtypeVal_comp (hs : IsOpen s) {x : s} {f : E → s} (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered (Subtype.val ∘ f) x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  have : Subtype.val ∘ f ⁻¹' (Subtype.val '' U) = f ⁻¹' U := by ext; simp
  ⟨inst, Subtype.val '' U, ⟨x, hxU, rfl⟩, hs.isOpenMap_subtype_val _ hU, by rwa [this], .trans
    (.setCongr this) (H.trans <| .prodCongr (IsEmbedding.subtypeVal.homeomorphImage U) (.refl I)),
    fun _ ↦ congr_arg Subtype.val (hH _)⟩

theorem comp_subtypeVal (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) {x : X} (hx : x ∈ s)
    (h : IsEvenlyCovered (fun e : f ⁻¹' s ↦ f e) x I) : IsEvenlyCovered f x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  (isEmpty_or_nonempty I).elim (fun _ ↦ .of_preimage_eq_empty _ ((hs.inter hU).mem_nhds ⟨hx, hxU⟩)
    <| Set.not_nonempty_iff_eq_empty.mp fun ⟨e, he⟩ ↦ isEmptyElim (H ⟨⟨e, he.1⟩, he.2⟩).2) fun _ ↦
  have hUs : U ⊆ s := fun y hy ↦ by
    convert Set.mem_preimage.mp (H.symm (⟨y, hy⟩, Classical.arbitrary I)).1.2; simp [← hH]
  have : Subtype.val '' ((fun e : f ⁻¹' s ↦ f e) ⁻¹' U) = f ⁻¹' U := by ext; simpa using @hUs _
  ⟨inst, U, hxU, hU, this ▸ hfs.isOpenMap_subtype_val _ hfU, .trans (.symm <| .trans
    (IsEmbedding.subtypeVal.homeomorphImage _) <| .setCongr this) H, fun x ↦ by
    dsimp; convert hH ⟨⟨x, hUs x.2⟩, x.2⟩ using 4; exact (Equiv.symm_apply_eq _).mpr rfl⟩

theorem comp_homeomorph {x : X} (h : IsEvenlyCovered f x I) {E'} [TopologicalSpace E']
    (g : E' ≃ₜ E) : IsEvenlyCovered (f ∘ g) x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, U, hxU, hU, hfU.preimage g.continuous, .trans (.trans
    (.setCongr <| by rw [Set.preimage_comp, g.image_symm]) (g.symm.image _).symm) H, fun _ ↦ hH _⟩

@[simp] theorem comp_homeomorph_iff {x : X} {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsEvenlyCovered (f ∘ g) x I ↔ IsEvenlyCovered f x I where
  mp h := by convert h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

theorem homeomorph_comp {x : X} (h : IsEvenlyCovered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsEvenlyCovered (g ∘ f) (g x) I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, g '' U, ⟨x, hxU, rfl⟩, g.isOpen_image.mpr hU, by simpa [Set.preimage_comp],
    .trans (.setCongr <| by simp [Set.preimage_comp]) (H.trans <| (g.image U).prodCongr (.refl I)),
    fun _ ↦ congr_arg g (hH _)⟩

@[simp] theorem homeomorph_comp_iff {x : X} {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsEvenlyCovered (g ∘ f) (g x) I ↔ IsEvenlyCovered f x I where
  mp h := by convert h.homeomorph_comp g.symm <;> ((try ext); simp)
  mpr h := h.homeomorph_comp g

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

theorem mono {t : Set X} (hf : IsCoveringMapOn f s) (ht : t ⊆ s) : IsCoveringMapOn f t :=
  fun x hx ↦ hf x (ht hx)

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

theorem restrictPreimage (hf : IsCoveringMapOn f s) (t : Set X) :
    IsCoveringMapOn (t.restrictPreimage f) (Subtype.val ⁻¹' s) :=
  fun x hs ↦ ((hf x hs).restrictPreimage t x.2).to_isEvenlyCovered_preimage

theorem comp_homeomorph (hf : IsCoveringMapOn f s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMapOn (f ∘ g) s :=
  fun x hx ↦ ((hf x hx).comp_homeomorph _).to_isEvenlyCovered_preimage

@[simp] theorem comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMapOn (f ∘ g) s ↔ IsCoveringMapOn f s where
  mp h := by convert h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

theorem homeomorph_comp (hf : IsCoveringMapOn f s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s) :=
  fun y hy ↦ (g.apply_symm_apply y ▸ (hf _ hy).homeomorph_comp _).to_isEvenlyCovered_preimage

@[simp] theorem homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s) ↔ IsCoveringMapOn f s where
  mp h := by convert h.homeomorph_comp g.symm <;> (ext; simp)
  mpr h := h.homeomorph_comp g

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})

variable {f}

theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) : IsCoveringMapOn f .univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf

theorem IsCoveringMapOn.isCoveringMap_restrictPreimage (hf : IsCoveringMapOn f s) :
    IsCoveringMap (s.restrictPreimage f) :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| by simpa using hf.restrictPreimage s

theorem IsCoveringMapOn.of_isCoveringMap_restrictPreimage (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s))
    (hf : IsCoveringMap (s.restrictPreimage f)) : IsCoveringMapOn f s := fun x hx ↦
  (((hf ⟨x, hx⟩).subtypeVal_comp _ hs).comp_subtypeVal _ hs hfs hx).to_isEvenlyCovered_preimage

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

variable {A} [TopologicalSpace A] {s : Set A} {g g₁ g₂ : A → E}

/-- Proposition 1.34 of [hatcher02]. -/
theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha

theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', f (g a) = f (g a')) (a a') : g a = g a' :=
  hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'

theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ :=
  hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha

theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, f (g a) = f (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'

theorem restrictPreimage (t : Set X) : IsCoveringMap (t.restrictPreimage f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.restrictPreimage t

theorem comp_homeomorph {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.comp_homeomorph g

theorem homeomorph_comp {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMap (g ∘ f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.homeomorph_comp g

omit hf

theorem comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMap (f ∘ g) ↔ IsCoveringMap f where
  mp h := by convert h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g

theorem homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMap (g ∘ f) ↔ IsCoveringMap f where
  mp h := by convert h.homeomorph_comp g.symm; ext; simp
  mpr h := h.homeomorph_comp g

end IsCoveringMap

theorem IsCoveringMapOn.of_isCoveringMap_subtype {s : Set X} (hs : IsOpen s) {f : E → X}
    (h : ∀ x, f x ∈ s) (hf : IsCoveringMap fun x ↦ (⟨f x, h x⟩ : s)) : IsCoveringMapOn f s :=
  have eq : f ⁻¹' s = .univ := by simpa [Set.range, Set.subset_def] using h
  of_isCoveringMap_restrictPreimage _ hs (by simp [eq]) <|
    hf.comp_homeomorph ((Homeomorph.setCongr eq).trans (Homeomorph.Set.univ E))

variable {f}

protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)

protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩

open Function in
/-- Let `f : E → X` be a (not necessarily continuous) map between topological spaces, and let
`V` be an open subset of `X`. Suppose that there is a family `U` of disjoint subsets of `E`
that covers `f⁻¹(V)` such that for every `i`,

 1. `f` is injective on `Uᵢ`,
 2. `V` is contained in the image `f(Uᵢ)`,
 3. the open sets in `V` are determined by their preimages in `Uᵢ`.

Then `f` admits a `Trivialization` over the base set `V`. -/
@[simps source target baseSet] noncomputable def IsOpen.trivializationDiscrete [Nonempty (X → E)]
    {ι} [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] (U : ι → Set E) (V : Set X)
    (open_V : IsOpen V) (open_iff : ∀ i {W}, W ⊆ V → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i)))
    (inj : ∀ i, (U i).InjOn f) (surj : ∀ i, (U i).SurjOn f V)
    (disjoint : Pairwise (Disjoint on U)) (exhaustive : f ⁻¹' V ⊆ ⋃ i, U i) :
    Trivialization ι f := by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : PartialEquiv E (X × ι) :=
  { toFun e := (f e, if he : f e ∈ V then idx e he else Classical.arbitrary ι),
    invFun x := if hx : x.1 ∈ V then inv x.2 hx else Classical.arbitrary (X → E) x.1,
    source := f ⁻¹' V,
    target := V ×ˢ Set.univ,
    map_source' x hx := ⟨hx, ⟨⟩⟩
    map_target' x hx := by rw [dif_pos hx.1]; apply (f_inv _ hx.1).symm ▸ hx.1,
    left_inv' e he := by
      simp_rw [dif_pos (id he : f e ∈ V)]
      exact inj _ (inv_U _ he) (idx_U e he) (f_inv _ _)
    right_inv' x hx := by
      rw [dif_pos hx.1]
      refine Prod.ext (f_inv _ hx.1) ?_
      rw [dif_pos ((f_inv _ hx.1).symm ▸ hx.1)]
      by_contra h; exact (disjoint h).le_bot ⟨idx_U .., inv_U _ _⟩ }
  have open_preim {W} (hWV : W ⊆ V) (open_W : IsOpen W) : IsOpen (f ⁻¹' W) := by
    convert isOpen_iUnion (fun i ↦ (open_iff i hWV).mp open_W)
    rw [← Set.inter_iUnion, eq_comm, Set.inter_eq_left]
    exact (Set.preimage_mono hWV).trans exhaustive'
  have open_source : IsOpen F.source := open_preim subset_rfl open_V
  have cont_f : ContinuousOn f F.source := (continuousOn_open_iff open_source).mpr
    fun W open_W ↦ open_preim Set.inter_subset_left (open_V.inter open_W)
  refine
  { toPartialEquiv := F,
    open_source := open_source,
    open_target := open_V.prod isOpen_univ,
    continuousOn_toFun := cont_f.prodMk <| continuousOn_of_forall_continuousAt fun e he ↦
      continuous_const (y := idx e he) |>.continuousAt.congr <| mem_nhds_iff.mpr
        ⟨U (idx e he) ∩ F.source, fun e' he' ↦ ?_, ?_, idx_U e he, he⟩
    continuousOn_invFun := continuousOn_prod_of_discrete_right.mpr fun i ↦ ?_,
    baseSet := V,
    open_baseSet := open_V,
    source_eq := rfl,
    target_eq := rfl,
    proj_toFun _ _ := rfl }
  · by_contra h; apply (disjoint h).le_bot
    · dsimp only; rw [dif_pos (by exact he'.2)]; exact ⟨he'.1, idx_U ..⟩
  · rwa [Set.inter_comm, ← open_iff _ subset_rfl]
  · simp_rw [F, Set.prodMk_mem_set_prod_eq, Set.mem_univ, and_true]
    refine (continuousOn_open_iff open_V).mpr fun W open_W ↦ ?_
    rw [open_iff i Set.inter_subset_left]
    convert ((open_iff i subset_rfl).mp open_V).inter open_W using 1
    refine Set.ext fun e ↦ and_right_comm.trans (and_congr_right fun ⟨hV, hU⟩ ↦ ?_)
    rw [Set.mem_preimage, dif_pos hV, inj i (inv_U i _) hU (f_inv i _)]

variable {s}

variable (f) in
theorem IsDiscrete.of_openPartialHomeomorph {t : Set E} {x : X}
    (htx : t ⊆ f ⁻¹' {x}) (hf : ∀ e ∈ t, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsDiscrete t :=
  isDiscrete_iff_forall_exists_isOpen.mpr fun e he ↦ by
    obtain ⟨φ, hφ, rfl⟩ := hf e he
    exact ⟨_, φ.open_source, subset_antisymm (fun e' he' ↦ φ.injOn he'.1 hφ <|
      (htx he'.2).trans (htx he).symm) <| Set.singleton_subset_iff.mpr ⟨hφ, he⟩⟩

open Set in
/-- If `f : E → X` is a closed map between topological spaces with `E` Hausdorff, such that the
fiber over a point `x : X` is finite and `f` restricts to a homeomorphism on a neighborhood of
every point of the fiber, then `x` admits an evenly covered neighborhood. -/
theorem IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph [T2Space E] {x : X}
    (hf : IsClosedMap f) (fin : (f ⁻¹' {x}).Finite)
    (h : ∀ e ∈ f ⁻¹' {x}, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) := by
  have : DiscreteTopology (f ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl h).1
  /- for each preimage e of x, choose a homeomorphism φₑ
    from a neighborhood of e to its image -/
  choose φ hφ using fun e : f ⁻¹' {x} ↦ h e e.2
  -- separately, choose pairwise disjoint neighborhoods Vₑ by Hausdorff-ness
  have ⟨V, hV, disj⟩ := fin.t2_separation
  -- let Vₑ' be the intersection Vₑ ∩ dom(φₑ)
  let V' (e : f ⁻¹' {x}) := V e ∩ (φ e).source
  have hV' e : IsOpen (V' e) := (hV e).2.inter (φ e).open_source
  have : ⋃ e, V' e ∈ nhdsSet (f ⁻¹' {x}) :=
    (isOpen_iUnion hV').mem_nhdsSet.2 fun e he ↦ mem_iUnion_of_mem ⟨e, he⟩ ⟨(hV e).1, (hφ _).1⟩
  -- since f is a closed map, the union of the Vₑ' contains the preimage of a neighborhood U of x
  have ⟨W, hWx, hWV⟩ := isClosedMap_iff_comap_nhds_le.mp hf this
  cases isEmpty_or_nonempty (f ⁻¹' {x})
  · exact .of_preimage_eq_empty _ hWx (by simpa using hWV)
  have ⟨U, hUW, hU, hxU⟩ := mem_nhds_iff.mp hWx
  -- show that the intersection of U with the images of Vₑ' is evenly covered
  let U' := U ∩ ⋂ e : f ⁻¹' {x}, f '' (V' e)
  have : Finite (f ⁻¹' {x}) := fin
  have hU' : IsOpen U' := hU.inter <| isOpen_iInter_of_finite fun e ↦ by
    convert ← (φ e).isOpen_image_of_subset_source (hV' _) inter_subset_right; exact (hφ e).2
  have hUV e : U' ⊆ f '' V' e := inter_subset_right.trans (iInter_subset ..)
  have : Nonempty E := ⟨Classical.arbitrary (f ⁻¹' {x})⟩
  refine .of_trivialization (t := hU'.trivializationDiscrete _ _
    (fun e s hs ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩) (fun e ↦ ?_)
    (fun e ↦ .mono subset_rfl (hUV e) (surjOn_image f _))
    (pairwise_disjoint_mono disj.subtype fun e ↦ inter_subset_left)
    ((preimage_mono (inter_subset_left.trans hUW)).trans hWV))
    ⟨hxU, Set.mem_iInter.mpr fun e ↦ ⟨e, ⟨(hV e).1, (hφ e).1⟩, e.2⟩⟩
  · convert ((φ e).isOpen_inter_preimage h).inter (hV e).2 using 1
    simp_rw [(hφ e).2, V']; ac_rfl
  · have : s ⊆ (φ e).target := hs.trans <| (hUV e).trans <| by
      rw [← (φ e).image_source_eq_target, (hφ e).2]; exact image_mono inter_subset_right
    rw [← (φ e).isOpen_symm_image_iff_of_subset_target this,
      (φ e).symm_image_eq_source_inter_preimage this, (hφ e).2, inter_comm]
    convert h using 1
    refine inter_eq_inter_iff_left.mpr ⟨fun e' h ↦ h.2.2, fun e' h ↦ ⟨?_ , h.2⟩⟩
    have ⟨e'', ⟨_, mem⟩, eq⟩ := mem_iInter.mp (hs h.1).2 e
    rwa [← (φ e).injOn mem h.2 (by rwa [(hφ e).2])]
  · convert ← (φ e).injOn.mono inter_subset_right; exact (hφ e).2

/-- If `f : E → X` is a closed map between topological spaces with `E` Hausdorff, and `s` is
a subset of `X` on which `f` has finite fibers, such that `f` restricts to a homeomorphism on
a neighborhood of every point of `f ⁻¹' s`, then `f` is a covering map on `s`. -/
theorem IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph [T2Space E]
    (hf : IsClosedMap f) (hs : ∀ x ∈ s, (f ⁻¹' {x}).Finite)
    (h : ∀ e ∈ f ⁻¹' s, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsCoveringMapOn f s :=
  fun x hx ↦ hf.isEvenlyCovered_of_openPartialHomeomorph (hs x hx) fun e he ↦ h e (by apply he ▸ hx)

/-- If `f : E → X` is a continuous map between Hausdorff spaces with `E` compact,
and `f` restricts to a homeomorphism on a neighborhood of every point of a fiber `f ⁻¹' {x}`,
then `x` admits an evenly covered neighborhood. -/
theorem IsEvenlyCovered.of_openPartialHomeomorph
    [T2Space E] [T2Space X] [CompactSpace E] {x : X} (hf : Continuous f)
    (h : ∀ e ∈ f ⁻¹' {x}, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    ((isClosed_singleton.preimage hf).isCompact.finite (.of_openPartialHomeomorph f subset_rfl h)) h

/-- If `f : E → X` is a continuous map between Hausdorff spaces with `E` compact, `s` is a subset
of `X` such that `f` restricts to a homeomorphism on a neighborhood of every point of `f ⁻¹' s`,
then `f` is a covering map on `s`.

For example, `s` can be taken to be the set of regular values of a C¹ map `f : E → X`
where `E` and `X` are manifolds of the same dimension with `E` compact, according to
the inverse function theorem (see `ContDiffAt.toOpenPartialHomeomorph`). -/
theorem IsCoveringMapOn.of_openPartialHomeomorph
    [T2Space E] [T2Space X] [CompactSpace E] (hf : Continuous f)
    (h : ∀ e ∈ f ⁻¹' s, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsCoveringMapOn f s :=
  fun x hx ↦ .of_openPartialHomeomorph hf fun e he ↦ h e (by apply he ▸ hx)

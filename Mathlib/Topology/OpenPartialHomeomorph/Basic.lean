/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens
/-!
# Partial homeomorphisms: basic theory


## Main definitions

* `OpenPartialHomeomorph.refl`: the identity open partial homeomorphism
* `Topology.IsOpenEmbedding.toOpenPartialHomeomorph`: construct a partial homeomorphism from an
  open embedding
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

/-- The identity on the whole space as an open partial homeomorphism. -/
@[simps! (attr := mfld_simps) -fullyApplied apply, simps! -isSimp source target]
protected def refl (X : Type*) [TopologicalSpace X] : OpenPartialHomeomorph X X :=
  (Homeomorph.refl X).toOpenPartialHomeomorph

@[simp, mfld_simps]
theorem refl_partialEquiv : (OpenPartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp, mfld_simps]
theorem refl_symm : (OpenPartialHomeomorph.refl X).symm = OpenPartialHomeomorph.refl X :=
  rfl

variable (e : OpenPartialHomeomorph X Y)

theorem source_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo

theorem image_eq_target_inter_inv_preimage {s : Set X} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h

theorem image_source_inter_eq' (s : Set X) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s

theorem image_source_inter_eq (s : Set X) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) :=
  e.toPartialEquiv.image_source_inter_eq s

theorem symm_image_eq_source_inter_preimage {s : Set Y} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

theorem symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _

theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.source ∩ s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s

theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

theorem source_inter_preimage_target_inter (s : Set Y) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s

theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target

theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

theorem isOpen_inter_preimage {s : Set Y} (hs : IsOpen s) : IsOpen (e.source ∩ e ⁻¹' s) :=
  e.continuousOn.isOpen_inter_preimage e.open_source hs

theorem isOpen_inter_preimage_symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target ∩ e.symm ⁻¹' s) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target hs

/-- An open partial homeomorphism is an open map on its source:
  the image of an open subset of the source is open. -/
lemma isOpen_image_of_subset_source {s : Set X} (hs : IsOpen s) (hse : s ⊆ e.source) :
    IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs

/-- The image of the restriction of an open set to the source is open. -/
theorem isOpen_image_source_inter {s : Set X} (hs : IsOpen s) :
    IsOpen (e '' (e.source ∩ s)) :=
  e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left

/-- The inverse of an open partial homeomorphism `e` is an open map on `e.target`. -/
lemma isOpen_image_symm_of_subset_target {t : Set Y} (ht : IsOpen t) (hte : t ⊆ e.target) :
    IsOpen (e.symm '' t) :=
  isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)

lemma isOpen_symm_image_iff_of_subset_target {t : Set Y} (hs : t ⊆ e.target) :
    IsOpen (e.symm '' t) ↔ IsOpen t := by
  refine ⟨fun h ↦ ?_, fun h ↦ e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t ⊆ e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h hs'

theorem isOpen_image_iff_of_subset_source {s : Set X} (hs : s ⊆ e.source) :
    IsOpen (e '' s) ↔ IsOpen s := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs, e.symm_symm]

/-- A `PartialEquiv` with continuous open forward map and open source is a
`OpenPartialHomeomorph`. -/
@[simps toPartialEquiv]
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) : OpenPartialHomeomorph X Y where
  toPartialEquiv := e
  open_source := hs
  open_target := by simpa only [range_restrict, e.image_source_eq_target] using ho.isOpen_range
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

@[simp]
theorem coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpenRestrict e hc ho hs) = e :=
  rfl

@[simp]
theorem coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpenRestrict e hc ho hs).symm = e.symm :=
  rfl

/-- A `PartialEquiv` with continuous open forward map and open source is a
`OpenPartialHomeomorph`. -/
@[simps! toPartialEquiv]
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : OpenPartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs

@[simp]
theorem coe_ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs) = e :=
  rfl

@[simp]
theorem coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs).symm = e.symm :=
  rfl

/-- The homeomorphism obtained by restricting an `OpenPartialHomeomorph` to a subset of the source.
-/
@[simps]
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s ⊆ e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo_iff_image_subset.2 ht.subset
  have h₂ : t ⊆ e.target := ht ▸ e.image_source_eq_target ▸ image_mono hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
    right_inv := fun b => Subtype.ext <| e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).mapsToRestrict h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).mapsToRestrict h₃ }

/-- An open partial homeomorphism defines a homeomorphism between its source and target. -/
@[simps!]
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target

theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology

theorem nhds_eq_comap_inf_principal {x} (hx : x ∈ e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2, ← map_nhds_subtype_val, ← map_comap_setCoe_val,
    e.toHomeomorphSourceTarget.nhds_eq_comap, nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]

/-- If an open partial homeomorphism has source and target equal to univ, then it induces a
homeomorphism between the whole spaces, expressed in this definition. -/
@[simps (attr := mfld_simps) -fullyApplied apply symm_apply]
-- TODO: add a `PartialEquiv` version
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x :=
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv x :=
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuousOn_univ, h'] using e.continuousOn_symm

theorem isOpenEmbedding_restrict : IsOpenEmbedding (e.source.restrict e) := by
  refine .of_continuous_injective_isOpenMap (e.continuousOn.comp_continuous
    continuous_subtype_val Subtype.prop) e.injOn.injective fun V hV ↦ ?_
  rw [Set.restrict_eq, Set.image_comp]
  exact e.isOpen_image_of_subset_source (e.open_source.isOpenMap_subtype_val V hV)
    fun _ ⟨x, _, h⟩ ↦ h ▸ x.2

/-- An open partial homeomorphism whose source is all of `X` defines an open embedding of `X` into
`Y`. The converse is also true; see `IsOpenEmbedding.toOpenPartialHomeomorph`. -/
theorem to_isOpenEmbedding (h : e.source = Set.univ) : IsOpenEmbedding e :=
  e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding

end OpenPartialHomeomorph

/-!
## Open embeddings
-/
namespace Topology.IsOpenEmbedding

variable (f : X → Y) (h : IsOpenEmbedding f)

/-- An open embedding of `X` into `Y`, with `X` nonempty, defines an open partial homeomorphism
whose source is all of `X`. The converse is also true; see
`OpenPartialHomeomorph.to_isOpenEmbedding`. -/
@[simps! (attr := mfld_simps) -fullyApplied apply source target]
noncomputable def toOpenPartialHomeomorph [Nonempty X] : OpenPartialHomeomorph X Y :=
  OpenPartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ

@[deprecated (since := "2025-08-29")] alias toPartialHomeomorph := toOpenPartialHomeomorph

variable [Nonempty X]

lemma toOpenPartialHomeomorph_left_inv {x : X} : (h.toOpenPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f), OpenPartialHomeomorph.left_inv]
  exact Set.mem_univ _

@[deprecated (since := "2025-08-29")] alias
  toPartialHomeomorph_left_inv := toOpenPartialHomeomorph_left_inv

lemma toOpenPartialHomeomorph_right_inv {x : Y} (hx : x ∈ Set.range f) :
    f ((h.toOpenPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f), OpenPartialHomeomorph.right_inv]
  rwa [toOpenPartialHomeomorph_target]

@[deprecated (since := "2025-08-29")] alias
  toPartialHomeomorph_right_inv := toOpenPartialHomeomorph_right_inv

end Topology.IsOpenEmbedding

/-! inclusion of an open set in a topological space -/
namespace TopologicalSpace.Opens

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Opens X) (hs : Nonempty s)

/-- The inclusion of an open subset `s` of a space `X` into `X` is an open partial homeomorphism
from the subtype `s` to `X`. -/
noncomputable def openPartialHomeomorphSubtypeCoe : OpenPartialHomeomorph s X :=
  IsOpenEmbedding.toOpenPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal

@[deprecated (since := "2025-08-29")] alias
  partialHomeomorphSubtypeCoe := openPartialHomeomorphSubtypeCoe

@[simp, mfld_simps]
theorem openPartialHomeomorphSubtypeCoe_coe :
    (s.openPartialHomeomorphSubtypeCoe hs : s → X) = (↑) :=
  rfl

@[deprecated (since := "2025-08-29")] alias
  partialHomeomorphSubtypeCoe_coe := openPartialHomeomorphSubtypeCoe_coe

@[simp, mfld_simps]
theorem openPartialHomeomorphSubtypeCoe_source :
    (s.openPartialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[deprecated (since := "2025-08-29")] alias
  partialHomeomorphSubtypeCoe_source := openPartialHomeomorphSubtypeCoe_source

@[simp, mfld_simps]
theorem openPartialHomeomorphSubtypeCoe_target :
    (s.openPartialHomeomorphSubtypeCoe hs).target = s := by
  simp only [openPartialHomeomorphSubtypeCoe, Subtype.range_coe_subtype, mfld_simps]
  rfl

@[deprecated (since := "2025-08-29")] alias
  partialHomeomorphSubtypeCoe_target := openPartialHomeomorphSubtypeCoe_target

end TopologicalSpace.Opens

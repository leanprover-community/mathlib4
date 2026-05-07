/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.PartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Partial homeomorphisms: basic theory


## Main definitions

* `PartialHomeomorph.refl`: the identity open partial homeomorphism
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace PartialHomeomorph

/-- The identity on the whole space as an open partial homeomorphism. -/
@[simps! -fullyApplied apply, simps! -isSimp source target]
protected def refl (X : Type*) [TopologicalSpace X] : PartialHomeomorph X X :=
  (Homeomorph.refl X).toPartialHomeomorph

@[simp]
theorem refl_partialEquiv : (PartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp]
theorem refl_symm : (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X :=
  rfl

variable (e : PartialHomeomorph X Y)

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

/-- A `PartialEquiv` with continuous open forward map and open source is a `PartialHomeomorph`. -/
@[simps toPartialEquiv]
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) : PartialHomeomorph X Y where
  toPartialEquiv := e
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

@[simp]
theorem coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) : ⇑(ofContinuousOpenRestrict e hc ho) = e :=
  rfl

@[simp]
theorem coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.restrict e)) :
    ⇑(ofContinuousOpenRestrict e hc ho).symm = e.symm :=
  rfl

/-- A `PartialEquiv` with continuous open forward map and open source is a `PartialHomeomorph`. -/
@[simps! toPartialEquiv]
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.restrict hs)

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

/-- If an open partial homeomorphism has source and target equal to univ, then it induces a
homeomorphism between the whole spaces, expressed in this definition. -/
@[simps -fullyApplied apply symm_apply]
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

theorem isEmbedding_restrict : IsEmbedding (e.source.restrict e.toFun) := by
  rw [isEmbedding_iff]
  constructor
  · apply Topology.IsInducing.of_codRestrict (t := e.target) (by simp)
    rw [← PartialEquiv.toEquiv_eq_codRestrict_restrict]
    exact e.toHomeomorphSourceTarget.isInducing
  · rw [coe_coe, restrict_eq, e.injOn.injective_iff e.source (by simp)]
    exact Subtype.val_injective

/-- A partial homeomorphism whose source is all of `X` defines an embedding of `X` into
`Y`. The converse is also true; see `IsEmbedding.toPartialHomeomorph`. -/
theorem to_isEmbedding (h : e.source = Set.univ) : IsEmbedding e :=
  e.isEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isEmbedding

/-- If a `PartialEquiv` is a homeomorphism when restricted to source and target, then it is a
`PartialHomeomorph`. -/
def ofIsHomeomorphToEquiv (f : PartialEquiv X Y) (h : IsHomeomorph (f.toEquiv)) :
    PartialHomeomorph X Y where
  toPartialEquiv := f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict,
      ← continuous_codRestrict_iff (s := f.target) (by simp)]
    have : codRestrict (f.target.restrict f.invFun) f.source (by simp) = f.toEquiv.symm := by
      ext x
      simp [PartialEquiv.toEquiv]
    exact h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict,
      ← continuous_codRestrict_iff (s := f.source) (by simp),
      ← PartialEquiv.toEquiv_eq_codRestrict_restrict_invFun]
    exact ((Equiv.isHomeomorph_iff _).1 h).2

end PartialHomeomorph

/-!
## Embeddings
-/

namespace Topology.IsEmbedding

variable (f : X → Y) (h : IsEmbedding f)

/-- An embedding of `X` into `Y`, with `X` nonempty, defines a partial homeomorphism
whose source is all of `X`. The converse is also true; see
`PartialHomeomorph.to_isEmbedding`. -/
@[simps! -fullyApplied apply source target]
noncomputable def toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y :=
  PartialHomeomorph.ofIsHomeomorphToEquiv (h.injective.injOn.toPartialEquiv f univ) (by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    constructor
    · rw [PartialEquiv.toEquiv_eq_codRestrict_restrict]
      apply IsEmbedding.codRestrict
      simp only [InjOn.toPartialEquiv.eq_1, BijOn.toPartialEquiv_source, restrict_eq]
      exact h.comp subtypeVal
    · exact Equiv.surjective _)

variable [Nonempty X]

lemma toPartialHomeomorph_left_inv {x : X} : (h.toPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.left_inv]
  exact Set.mem_univ _

lemma toPartialHomeomorph_right_inv {x : Y} (hx : x ∈ Set.range f) :
    f ((h.toPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f), PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

end Topology.IsEmbedding

/-! inclusion of an open set in a topological space -/
namespace Set

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Set X) (hs : Nonempty s)

/-- The inclusion of an open subset `s` of a space `X` into `X` is an open partial homeomorphism
from the subtype `s` to `X`. -/
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s X :=
  IsEmbedding.subtypeVal.toPartialHomeomorph _

@[simp]
theorem partialHomeomorphSubtypeCoe_coe :
    (s.partialHomeomorphSubtypeCoe hs : s → X) = (↑) :=
  rfl

@[simp, mfld_simps]
theorem partialHomeomorphSubtypeCoe_source :
    (s.partialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[simp]
theorem partialHomeomorphSubtypeCoe_target :
    (s.partialHomeomorphSubtypeCoe hs).target = s := by
  simp [partialHomeomorphSubtypeCoe]

end Set

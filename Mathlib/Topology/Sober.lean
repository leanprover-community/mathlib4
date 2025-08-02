/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sets.OpenCover

/-!
# Sober spaces

A quasi-sober space is a topological space where every irreducible closed subset has a generic
point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[QuasiSober α] [T0Space α]`.

## Main definition

* `IsGenericPoint` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `QuasiSober` : A space is quasi-sober if every irreducible closed subset has a generic point.
* `genericPoints` : The set of generic points of irreducible components.

-/


open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

section genericPoint

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
@[stacks 004X "(1)"]
def IsGenericPoint (x : α) (S : Set α) : Prop :=
  closure ({x} : Set α) = S

theorem isGenericPoint_def {x : α} {S : Set α} : IsGenericPoint x S ↔ closure ({x} : Set α) = S :=
  Iff.rfl

theorem IsGenericPoint.def {x : α} {S : Set α} (h : IsGenericPoint x S) :
    closure ({x} : Set α) = S :=
  h

theorem isGenericPoint_closure {x : α} : IsGenericPoint x (closure ({x} : Set α)) :=
  refl _

variable {x y : α} {S U Z : Set α}

theorem isGenericPoint_iff_specializes : IsGenericPoint x S ↔ ∀ y, x ⤳ y ↔ y ∈ S := by
  simp only [specializes_iff_mem_closure, IsGenericPoint, Set.ext_iff]

namespace IsGenericPoint

theorem specializes_iff_mem (h : IsGenericPoint x S) : x ⤳ y ↔ y ∈ S :=
  isGenericPoint_iff_specializes.1 h y

protected theorem specializes (h : IsGenericPoint x S) (h' : y ∈ S) : x ⤳ y :=
  h.specializes_iff_mem.2 h'

protected theorem mem (h : IsGenericPoint x S) : x ∈ S :=
  h.specializes_iff_mem.1 specializes_rfl

protected theorem isClosed (h : IsGenericPoint x S) : IsClosed S :=
  h.def ▸ isClosed_closure

protected theorem isIrreducible (h : IsGenericPoint x S) : IsIrreducible S :=
  h.def ▸ isIrreducible_singleton.closure

protected theorem inseparable (h : IsGenericPoint x S) (h' : IsGenericPoint y S) :
    Inseparable x y :=
  (h.specializes h'.mem).antisymm (h'.specializes h.mem)

/-- In a T₀ space, each set has at most one generic point. -/
protected theorem eq [T0Space α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S) : x = y :=
  (h.inseparable h').eq

theorem mem_open_set_iff (h : IsGenericPoint x S) (hU : IsOpen U) : x ∈ U ↔ (S ∩ U).Nonempty :=
  ⟨fun h' => ⟨x, h.mem, h'⟩, fun ⟨_y, hyS, hyU⟩ => (h.specializes hyS).mem_open hU hyU⟩

theorem disjoint_iff (h : IsGenericPoint x S) (hU : IsOpen U) : Disjoint S U ↔ x ∉ U := by
  rw [h.mem_open_set_iff hU, ← not_disjoint_iff_nonempty_inter, Classical.not_not]

theorem mem_closed_set_iff (h : IsGenericPoint x S) (hZ : IsClosed Z) : x ∈ Z ↔ S ⊆ Z := by
  rw [← h.def, hZ.closure_subset_iff, singleton_subset_iff]

protected theorem image (h : IsGenericPoint x S) {f : α → β} (hf : Continuous f) :
    IsGenericPoint (f x) (closure (f '' S)) := by
  rw [isGenericPoint_def, ← h.def, ← image_singleton, closure_image_closure hf]

end IsGenericPoint

theorem isGenericPoint_iff_forall_closed (hS : IsClosed S) (hxS : x ∈ S) :
    IsGenericPoint x S ↔ ∀ Z : Set α, IsClosed Z → x ∈ Z → S ⊆ Z := by
  have : closure {x} ⊆ S := closure_minimal (singleton_subset_iff.2 hxS) hS
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_and, closure, subset_sInter_iff,
    mem_setOf_eq, and_imp, singleton_subset_iff]

end genericPoint

section Sober

/-- A space is sober if every irreducible closed subset has a generic point. -/
@[mk_iff, stacks 004X "(3)"]
class QuasiSober (α : Type*) [TopologicalSpace α] : Prop where
  sober : ∀ {S : Set α}, IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S

/-- A generic point of the closure of an irreducible space. -/
noncomputable def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    α :=
  (QuasiSober.sober hS.closure isClosed_closure).choose

theorem IsIrreducible.isGenericPoint_genericPoint_closure
    [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    IsGenericPoint hS.genericPoint (closure S) :=
  (QuasiSober.sober hS.closure isClosed_closure).choose_spec

theorem IsIrreducible.isGenericPoint_genericPoint [QuasiSober α] {S : Set α}
    (hS : IsIrreducible S) (hS' : IsClosed S) :
    IsGenericPoint hS.genericPoint S := by
  convert hS.isGenericPoint_genericPoint_closure; exact hS'.closure_eq.symm

@[simp]
theorem IsIrreducible.genericPoint_closure_eq [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    closure ({hS.genericPoint} : Set α) = closure S :=
  hS.isGenericPoint_genericPoint_closure

theorem IsIrreducible.closure_genericPoint [QuasiSober α] {S : Set α}
    (hS : IsIrreducible S) (hS' : IsClosed S) :
    closure ({hS.genericPoint} : Set α) = S :=
  hS.isGenericPoint_genericPoint_closure.trans hS'.closure_eq

variable (α)

/-- A generic point of a sober irreducible space. -/
noncomputable def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.isIrreducible_univ α).genericPoint

theorem genericPoint_spec [QuasiSober α] [IrreducibleSpace α] :
    IsGenericPoint (genericPoint α) univ := by
  simpa using (IrreducibleSpace.isIrreducible_univ α).isGenericPoint_genericPoint_closure

@[simp]
theorem genericPoint_closure [QuasiSober α] [IrreducibleSpace α] :
    closure ({genericPoint α} : Set α) = univ :=
  genericPoint_spec α

variable {α}

theorem genericPoint_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : genericPoint α ⤳ x :=
  (IsIrreducible.isGenericPoint_genericPoint_closure _).specializes (by simp)

attribute [local instance] specializationOrder

/-- The closed irreducible subsets of a sober space bijects with the points of the space. -/
noncomputable def irreducibleSetEquivPoints [QuasiSober α] [T0Space α] :
    TopologicalSpace.IrreducibleCloseds α ≃o α where
  toFun s := s.2.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := by
    refine TopologicalSpace.IrreducibleCloseds.ext ?_
    simp only [IsIrreducible.genericPoint_closure_eq, TopologicalSpace.IrreducibleCloseds.coe_mk,
      closure_eq_iff_isClosed.mpr s.3]
    rfl
  right_inv x := isIrreducible_singleton.closure.isGenericPoint_genericPoint_closure.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
  map_rel_iff' := by
    rintro ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
    refine specializes_iff_closure_subset.trans ?_
    simp
    rfl

lemma Topology.IsClosedEmbedding.quasiSober {f : α → β} (hf : IsClosedEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    obtain ⟨y, -, rfl⟩ := hx.mem
    use y
    apply image_injective.mpr hf.injective
    rw [← hx.def, ← hf.closure_image_eq, image_singleton]

theorem Topology.IsOpenEmbedding.quasiSober {f : α → β} (hf : IsOpenEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    obtain ⟨T, hT, rfl⟩ := hf.isInducing.isClosed_iff.mp hS'
    rw [image_preimage_eq_inter_range] at hx hS''
    have hxT : x ∈ T := by
      rw [← hT.closure_eq]
      exact closure_mono inter_subset_left hx.mem
    obtain ⟨y, rfl⟩ : x ∈ range f := by
      rw [hx.mem_open_set_iff hf.isOpen_range]
      refine Nonempty.mono ?_ hS''.1
      simpa using subset_closure
    use y
    change _ = _
    rw [hf.isEmbedding.closure_eq_preimage_closure_image, image_singleton, show _ = _ from hx]
    apply image_injective.mpr hf.injective
    ext z
    simp only [image_preimage_eq_inter_range, mem_inter_iff, and_congr_left_iff]
    exact fun hy => ⟨fun h => hT.closure_eq ▸ closure_mono inter_subset_left h,
      fun h => subset_closure ⟨h, hy⟩⟩

lemma TopologicalSpace.IsOpenCover.quasiSober_iff_forall {ι : Type*} {U : ι → Opens α}
    (hU : TopologicalSpace.IsOpenCover U) : QuasiSober α ↔ ∀ i, QuasiSober (U i) := by
  refine ⟨fun h i ↦ (U i).isOpenEmbedding'.quasiSober, fun hU' ↦ (quasiSober_iff _).mpr ?_⟩
  · rintro t ⟨⟨x, hx⟩, h⟩ h'
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have H : IsIrreducible ((↑) ⁻¹' t : Set (U i)) :=
      ⟨⟨⟨x, hi⟩, hx⟩, h.preimage (U i).isOpenEmbedding'⟩
    use H.genericPoint
    apply le_antisymm
    · simpa [h'.closure_subset_iff, h'.closure_eq] using
        continuous_subtype_val.closure_preimage_subset _ H.isGenericPoint_genericPoint_closure.mem
    rw [← image_singleton, ← closure_image_closure continuous_subtype_val,
      H.isGenericPoint_genericPoint_closure.def]
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen h (U i).isOpen ⟨x, ⟨hx, hi⟩⟩).trans
      (closure_mono ?_)
    simpa only [inter_comm t, ← Subtype.image_preimage_coe] using Set.image_mono subset_closure

lemma TopologicalSpace.IsOpenCover.quasiSober {ι : Type*} {U : ι → Opens α}
    (hU : TopologicalSpace.IsOpenCover U) [∀ i, QuasiSober (U i)] : QuasiSober α :=
  hU.quasiSober_iff_forall.mpr ‹_›

/-- A space is quasi-sober if it can be covered by open quasi-sober subsets. -/
theorem quasiSober_of_open_cover (S : Set (Set α)) (hS : ∀ s : S, IsOpen (s : Set α))
    [∀ s : S, QuasiSober s] (hS' : ⋃₀ S = ⊤) : QuasiSober α :=
  TopologicalSpace.IsOpenCover.quasiSober (U := fun s : S ↦ ⟨s, hS s⟩) <| by
    simpa [TopologicalSpace.IsOpenCover, ← SetLike.coe_set_eq, sUnion_eq_iUnion] using hS'

/-- Any Hausdorff space is a quasi-sober space because any irreducible set is a singleton. -/
instance (priority := 100) T2Space.quasiSober [T2Space α] : QuasiSober α where
  sober h _ := by
    obtain ⟨x, rfl⟩ := isIrreducible_iff_singleton.mp h
    exact ⟨x, closure_singleton⟩

end Sober

section genericPoints

variable (α) in
/-- The set of generic points of irreducible components. -/
def genericPoints : Set α := { x | closure {x} ∈ irreducibleComponents α }

namespace genericPoints

/-- The irreducible component of a generic point -/
def component (x : genericPoints α) : irreducibleComponents α :=
  ⟨closure {x.1}, x.2⟩

lemma isGenericPoint (x : genericPoints α) : IsGenericPoint x.1 (component x).1 := rfl

lemma component_injective [T0Space α] : Function.Injective (component (α := α)) :=
  fun x y e ↦ Subtype.ext ((isGenericPoint x).eq (e ▸ isGenericPoint y))

/-- The generic point of an irreducible component. -/
noncomputable
def ofComponent [QuasiSober α] (x : irreducibleComponents α) : genericPoints α :=
  ⟨x.2.1.genericPoint, show _ ∈ irreducibleComponents α from
    (x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)).symm ▸ x.2⟩

lemma isGenericPoint_ofComponent [QuasiSober α] (x : irreducibleComponents α) :
    IsGenericPoint (ofComponent x).1 x :=
    x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)

@[simp]
lemma component_ofComponent [QuasiSober α] (x : irreducibleComponents α) :
    component (ofComponent x) = x :=
  Subtype.ext (isGenericPoint_ofComponent x)

@[simp]
lemma ofComponent_component [T0Space α] [QuasiSober α] (x : genericPoints α) :
    ofComponent (component x) = x :=
  component_injective (component_ofComponent _)

lemma component_surjective [QuasiSober α] : Function.Surjective (component (α := α)) :=
  Function.HasRightInverse.surjective ⟨ofComponent, component_ofComponent⟩

lemma finite [T0Space α] (h : (irreducibleComponents α).Finite) : (genericPoints α).Finite :=
  @Finite.of_injective _ _ h _ component_injective

/-- In a sober space, the generic points corresponds bijectively to irreducible components -/
@[simps]
noncomputable
def equiv [T0Space α] [QuasiSober α] : genericPoints α ≃ irreducibleComponents α :=
  ⟨component, ofComponent, ofComponent_component, component_ofComponent⟩

lemma closure [QuasiSober α] : closure (genericPoints α) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x ↦ Set.subset_def.mp ?_ x mem_irreducibleComponent
  refine (isGenericPoint_ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).symm.trans_subset (closure_mono ?_)
  exact Set.singleton_subset_iff.mpr (ofComponent _).2

end genericPoints

lemma genericPoints_eq_singleton [QuasiSober α] [IrreducibleSpace α] [T0Space α] :
    genericPoints α = {genericPoint α} := by
  ext x
  rw [genericPoints, irreducibleComponents_eq_singleton]
  exact ⟨((genericPoint_spec α).eq · |>.symm), (· ▸ genericPoint_spec α)⟩

end genericPoints

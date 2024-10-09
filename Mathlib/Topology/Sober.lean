/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Separation
import Mathlib.Topology.Sets.Closeds

/-!
# Sober spaces

A quasi-sober space is a topological space where every
irreducible closed subset has a generic point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[QuasiSober α] [T0Space α]`.

## Main definition

* `IsGenericPoint` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `QuasiSober` : A space is quasi-sober if every irreducible closed subset has a generic point.

-/


open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

section genericPoint

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
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
@[mk_iff]
class QuasiSober (α : Type*) [TopologicalSpace α] : Prop where
  sober : ∀ {S : Set α}, IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S

/-- A generic point of the closure of an irreducible space. -/
noncomputable def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    α :=
  (QuasiSober.sober hS.closure isClosed_closure).choose

theorem IsIrreducible.genericPoint_spec [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    IsGenericPoint hS.genericPoint (closure S) :=
  (QuasiSober.sober hS.closure isClosed_closure).choose_spec

@[simp]
theorem IsIrreducible.genericPoint_closure_eq [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    closure ({hS.genericPoint} : Set α) = closure S :=
  hS.genericPoint_spec

variable (α)

/-- A generic point of a sober irreducible space. -/
noncomputable def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.isIrreducible_univ α).genericPoint

theorem genericPoint_spec [QuasiSober α] [IrreducibleSpace α] :
    IsGenericPoint (genericPoint α) ⊤ := by
  simpa using (IrreducibleSpace.isIrreducible_univ α).genericPoint_spec

@[simp]
theorem genericPoint_closure [QuasiSober α] [IrreducibleSpace α] :
    closure ({genericPoint α} : Set α) = ⊤ :=
  genericPoint_spec α

variable {α}

theorem genericPoint_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : genericPoint α ⤳ x :=
  (IsIrreducible.genericPoint_spec _).specializes (by simp)

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
  right_inv x := isIrreducible_singleton.closure.genericPoint_spec.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
  map_rel_iff' := by
    rintro ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
    refine specializes_iff_closure_subset.trans ?_
    simp [hs'.closure_eq, ht'.closure_eq]
    rfl

theorem ClosedEmbedding.quasiSober {f : α → β} (hf : ClosedEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    obtain ⟨y, -, rfl⟩ := hx.mem
    use y
    apply image_injective.mpr hf.inj
    rw [← hx.def, ← hf.closure_image_eq, image_singleton]

theorem OpenEmbedding.quasiSober {f : α → β} (hf : OpenEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    obtain ⟨T, hT, rfl⟩ := hf.toInducing.isClosed_iff.mp hS'
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
    rw [hf.toEmbedding.closure_eq_preimage_closure_image, image_singleton, show _ = _ from hx]
    apply image_injective.mpr hf.inj
    ext z
    simp only [image_preimage_eq_inter_range, mem_inter_iff, and_congr_left_iff]
    exact fun hy => ⟨fun h => hT.closure_eq ▸ closure_mono inter_subset_left h,
      fun h => subset_closure ⟨h, hy⟩⟩

/-- A space is quasi sober if it can be covered by open quasi sober subsets. -/
theorem quasiSober_of_open_cover (S : Set (Set α)) (hS : ∀ s : S, IsOpen (s : Set α))
    [hS' : ∀ s : S, QuasiSober s] (hS'' : ⋃₀ S = ⊤) : QuasiSober α := by
  rw [quasiSober_iff]
  intro t h h'
  obtain ⟨x, hx⟩ := h.1
  obtain ⟨U, hU, hU'⟩ : x ∈ ⋃₀ S := by
    rw [hS'']
    trivial
  haveI : QuasiSober U := hS' ⟨U, hU⟩
  have H : IsPreirreducible ((↑) ⁻¹' t : Set U) :=
    h.2.preimage (hS ⟨U, hU⟩).openEmbedding_subtype_val
  replace H : IsIrreducible ((↑) ⁻¹' t : Set U) := ⟨⟨⟨x, hU'⟩, by simpa using hx⟩, H⟩
  use H.genericPoint
  have := continuous_subtype_val.closure_preimage_subset _ H.genericPoint_spec.mem
  rw [h'.closure_eq] at this
  apply le_antisymm
  · apply h'.closure_subset_iff.mpr
    simpa using this
  rw [← image_singleton, ← closure_image_closure continuous_subtype_val, H.genericPoint_spec.def]
  refine (subset_closure_inter_of_isPreirreducible_of_isOpen h.2 (hS ⟨U, hU⟩) ⟨x, hx, hU'⟩).trans
    (closure_mono ?_)
  rw [inter_comm t, ← Subtype.image_preimage_coe]
  exact Set.image_subset _ subset_closure

/-- Any Hausdorff space is a quasi-sober space because any irreducible set is a singleton. -/
instance (priority := 100) T2Space.quasiSober [T2Space α] : QuasiSober α where
  sober h _ := by
    obtain ⟨x, rfl⟩ := isIrreducible_iff_singleton.mp h
    exact ⟨x, closure_singleton⟩

end Sober

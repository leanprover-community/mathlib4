/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Separation

#align_import topology.sober from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

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
#align is_generic_point IsGenericPoint

theorem isGenericPoint_def {x : α} {S : Set α} : IsGenericPoint x S ↔ closure ({x} : Set α) = S :=
  Iff.rfl
#align is_generic_point_def isGenericPoint_def

theorem IsGenericPoint.def {x : α} {S : Set α} (h : IsGenericPoint x S) :
    closure ({x} : Set α) = S :=
  h
#align is_generic_point.def IsGenericPoint.def

theorem isGenericPoint_closure {x : α} : IsGenericPoint x (closure ({x} : Set α)) :=
  refl _
#align is_generic_point_closure isGenericPoint_closure

variable {x y : α} {S U Z : Set α}

theorem isGenericPoint_iff_specializes : IsGenericPoint x S ↔ ∀ y, x ⤳ y ↔ y ∈ S := by
  simp only [specializes_iff_mem_closure, IsGenericPoint, Set.ext_iff]
  -- 🎉 no goals
#align is_generic_point_iff_specializes isGenericPoint_iff_specializes

namespace IsGenericPoint

theorem specializes_iff_mem (h : IsGenericPoint x S) : x ⤳ y ↔ y ∈ S :=
  isGenericPoint_iff_specializes.1 h y
#align is_generic_point.specializes_iff_mem IsGenericPoint.specializes_iff_mem

protected theorem specializes (h : IsGenericPoint x S) (h' : y ∈ S) : x ⤳ y :=
  h.specializes_iff_mem.2 h'
#align is_generic_point.specializes IsGenericPoint.specializes

protected theorem mem (h : IsGenericPoint x S) : x ∈ S :=
  h.specializes_iff_mem.1 specializes_rfl
#align is_generic_point.mem IsGenericPoint.mem

protected theorem isClosed (h : IsGenericPoint x S) : IsClosed S :=
  h.def ▸ isClosed_closure
#align is_generic_point.is_closed IsGenericPoint.isClosed

protected theorem isIrreducible (h : IsGenericPoint x S) : IsIrreducible S :=
  h.def ▸ isIrreducible_singleton.closure
#align is_generic_point.is_irreducible IsGenericPoint.isIrreducible

protected theorem inseparable (h : IsGenericPoint x S) (h' : IsGenericPoint y S) :
    Inseparable x y :=
  (h.specializes h'.mem).antisymm (h'.specializes h.mem)

/-- In a T₀ space, each set has at most one generic point. -/
protected theorem eq [T0Space α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S) : x = y :=
  (h.inseparable h').eq
#align is_generic_point.eq IsGenericPoint.eq

theorem mem_open_set_iff (h : IsGenericPoint x S) (hU : IsOpen U) : x ∈ U ↔ (S ∩ U).Nonempty :=
  ⟨fun h' => ⟨x, h.mem, h'⟩, fun ⟨_y, hyS, hyU⟩ => (h.specializes hyS).mem_open hU hyU⟩
#align is_generic_point.mem_open_set_iff IsGenericPoint.mem_open_set_iff

theorem disjoint_iff (h : IsGenericPoint x S) (hU : IsOpen U) : Disjoint S U ↔ x ∉ U := by
  rw [h.mem_open_set_iff hU, ← not_disjoint_iff_nonempty_inter, Classical.not_not]
  -- 🎉 no goals
#align is_generic_point.disjoint_iff IsGenericPoint.disjoint_iff

theorem mem_closed_set_iff (h : IsGenericPoint x S) (hZ : IsClosed Z) : x ∈ Z ↔ S ⊆ Z := by
  rw [← h.def, hZ.closure_subset_iff, singleton_subset_iff]
  -- 🎉 no goals
#align is_generic_point.mem_closed_set_iff IsGenericPoint.mem_closed_set_iff

protected theorem image (h : IsGenericPoint x S) {f : α → β} (hf : Continuous f) :
    IsGenericPoint (f x) (closure (f '' S)) := by
  rw [isGenericPoint_def, ← h.def, ← image_singleton, closure_image_closure hf]
  -- 🎉 no goals
#align is_generic_point.image IsGenericPoint.image

end IsGenericPoint

theorem isGenericPoint_iff_forall_closed (hS : IsClosed S) (hxS : x ∈ S) :
    IsGenericPoint x S ↔ ∀ Z : Set α, IsClosed Z → x ∈ Z → S ⊆ Z := by
  have : closure {x} ⊆ S := closure_minimal (singleton_subset_iff.2 hxS) hS
  -- ⊢ IsGenericPoint x S ↔ ∀ (Z : Set α), IsClosed Z → x ∈ Z → S ⊆ Z
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_and_iff, closure, subset_sInter_iff,
    mem_setOf_eq, and_imp, singleton_subset_iff]
#align is_generic_point_iff_forall_closed isGenericPoint_iff_forall_closed

end genericPoint

section Sober

/-- A space is sober if every irreducible closed subset has a generic point. -/
@[mk_iff quasiSober_iff]
class QuasiSober (α : Type*) [TopologicalSpace α] : Prop where
  sober : ∀ {S : Set α}, IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S
#align quasi_sober QuasiSober

/-- A generic point of the closure of an irreducible space. -/
noncomputable def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    α :=
  (QuasiSober.sober hS.closure isClosed_closure).choose
#align is_irreducible.generic_point IsIrreducible.genericPoint

theorem IsIrreducible.genericPoint_spec [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    IsGenericPoint hS.genericPoint (closure S) :=
  (QuasiSober.sober hS.closure isClosed_closure).choose_spec
#align is_irreducible.generic_point_spec IsIrreducible.genericPoint_spec

@[simp]
theorem IsIrreducible.genericPoint_closure_eq [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    closure ({hS.genericPoint} : Set α) = closure S :=
  hS.genericPoint_spec
#align is_irreducible.generic_point_closure_eq IsIrreducible.genericPoint_closure_eq

variable (α)

/-- A generic point of a sober irreducible space. -/
noncomputable def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.isIrreducible_univ α).genericPoint
#align generic_point genericPoint

theorem genericPoint_spec [QuasiSober α] [IrreducibleSpace α] : IsGenericPoint (genericPoint α) ⊤ :=
  by simpa using (IrreducibleSpace.isIrreducible_univ α).genericPoint_spec
     -- 🎉 no goals
#align generic_point_spec genericPoint_spec

@[simp]
theorem genericPoint_closure [QuasiSober α] [IrreducibleSpace α] :
    closure ({genericPoint α} : Set α) = ⊤ :=
  genericPoint_spec α
#align generic_point_closure genericPoint_closure

variable {α}

theorem genericPoint_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : genericPoint α ⤳ x :=
  (IsIrreducible.genericPoint_spec _).specializes (by simp)
                                                      -- 🎉 no goals
#align generic_point_specializes genericPoint_specializes

attribute [local instance] specializationOrder

/-- The closed irreducible subsets of a sober space bijects with the points of the space. -/
noncomputable def irreducibleSetEquivPoints [QuasiSober α] [T0Space α] :
    { s : Set α | IsIrreducible s ∧ IsClosed s } ≃o α where
  toFun s := s.prop.1.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := Subtype.eq <| Eq.trans s.prop.1.genericPoint_spec <|
    closure_eq_iff_isClosed.mpr s.2.2
  right_inv x := isIrreducible_singleton.closure.genericPoint_spec.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
          -- ⊢ IsGenericPoint x (closure {x})
                                -- 🎉 no goals
  map_rel_iff' := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    -- ⊢ ↑{ toFun := fun s => IsIrreducible.genericPoint (_ : IsIrreducible ↑s), invF …
    refine specializes_iff_closure_subset.trans ?_
    -- ⊢ closure {↑{ toFun := fun s => IsIrreducible.genericPoint (_ : IsIrreducible  …
    simp [hs.2.closure_eq, ht.2.closure_eq]
    -- 🎉 no goals
#align irreducible_set_equiv_points irreducibleSetEquivPoints

theorem ClosedEmbedding.quasiSober {f : α → β} (hf : ClosedEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    -- ⊢ ∃ x, IsGenericPoint x S✝
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    -- ⊢ ∃ x, IsGenericPoint x S✝
    obtain ⟨y, -, rfl⟩ := hx.mem
    -- ⊢ ∃ x, IsGenericPoint x S✝
    use y
    -- ⊢ IsGenericPoint y S✝
    apply image_injective.mpr hf.inj
    -- ⊢ f '' closure {y} = f '' S✝
    rw [← hx.def, ← hf.closure_image_eq, image_singleton]
    -- 🎉 no goals
#align closed_embedding.quasi_sober ClosedEmbedding.quasiSober

theorem OpenEmbedding.quasiSober {f : α → β} (hf : OpenEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    -- ⊢ ∃ x, IsGenericPoint x S✝
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    -- ⊢ ∃ x, IsGenericPoint x S✝
    obtain ⟨T, hT, rfl⟩ := hf.toInducing.isClosed_iff.mp hS'
    -- ⊢ ∃ x, IsGenericPoint x (f ⁻¹' T)
    rw [image_preimage_eq_inter_range] at hx hS''
    -- ⊢ ∃ x, IsGenericPoint x (f ⁻¹' T)
    have hxT : x ∈ T := by
      rw [← hT.closure_eq]
      exact closure_mono (inter_subset_left _ _) hx.mem
    obtain ⟨y, rfl⟩ : x ∈ range f := by
      rw [hx.mem_open_set_iff hf.open_range]
      refine' Nonempty.mono _ hS''.1
      simpa using subset_closure
    use y
    -- ⊢ IsGenericPoint y (f ⁻¹' T)
    change _ = _
    -- ⊢ closure {y} = f ⁻¹' T
    rw [hf.toEmbedding.closure_eq_preimage_closure_image, image_singleton, show _ = _ from hx]
    -- ⊢ f ⁻¹' closure (T ∩ range f) = f ⁻¹' T
    apply image_injective.mpr hf.inj
    -- ⊢ f '' (f ⁻¹' closure (T ∩ range f)) = f '' (f ⁻¹' T)
    ext z
    -- ⊢ z ∈ f '' (f ⁻¹' closure (T ∩ range f)) ↔ z ∈ f '' (f ⁻¹' T)
    simp only [image_preimage_eq_inter_range, mem_inter_iff, and_congr_left_iff]
    -- ⊢ z ∈ range f → (z ∈ closure (T ∩ range f) ↔ z ∈ T)
    exact fun hy => ⟨fun h => hT.closure_eq ▸ closure_mono (inter_subset_left _ _) h,
      fun h => subset_closure ⟨h, hy⟩⟩
#align open_embedding.quasi_sober OpenEmbedding.quasiSober

/-- A space is quasi sober if it can be covered by open quasi sober subsets. -/
theorem quasiSober_of_open_cover (S : Set (Set α)) (hS : ∀ s : S, IsOpen (s : Set α))
    [hS' : ∀ s : S, QuasiSober s] (hS'' : ⋃₀ S = ⊤) : QuasiSober α := by
  rw [quasiSober_iff]
  -- ⊢ ∀ {S : Set α}, IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S
  intro t h h'
  -- ⊢ ∃ x, IsGenericPoint x t
  obtain ⟨x, hx⟩ := h.1
  -- ⊢ ∃ x, IsGenericPoint x t
  obtain ⟨U, hU, hU'⟩ : x ∈ ⋃₀ S := by
    rw [hS'']
    trivial
  haveI : QuasiSober U := hS' ⟨U, hU⟩
  -- ⊢ ∃ x, IsGenericPoint x t
  have H : IsPreirreducible ((↑) ⁻¹' t : Set U) :=
    h.2.preimage (hS ⟨U, hU⟩).openEmbedding_subtype_val
  replace H : IsIrreducible ((↑) ⁻¹' t : Set U) := ⟨⟨⟨x, hU'⟩, by simpa using hx⟩, H⟩
  -- ⊢ ∃ x, IsGenericPoint x t
  use H.genericPoint
  -- ⊢ IsGenericPoint (↑(IsIrreducible.genericPoint H)) t
  have := continuous_subtype_val.closure_preimage_subset _ H.genericPoint_spec.mem
  -- ⊢ IsGenericPoint (↑(IsIrreducible.genericPoint H)) t
  rw [h'.closure_eq] at this
  -- ⊢ IsGenericPoint (↑(IsIrreducible.genericPoint H)) t
  apply le_antisymm
  -- ⊢ closure {↑(IsIrreducible.genericPoint H)} ≤ t
  · apply h'.closure_subset_iff.mpr
    -- ⊢ {↑(IsIrreducible.genericPoint H)} ⊆ t
    simpa using this
    -- 🎉 no goals
  rw [← image_singleton, ← closure_image_closure continuous_subtype_val, H.genericPoint_spec.def]
  -- ⊢ t ≤ closure (Subtype.val '' closure (Subtype.val ⁻¹' t))
  refine' (subset_closure_inter_of_isPreirreducible_of_isOpen h.2 (hS ⟨U, hU⟩) ⟨x, hx, hU'⟩).trans
    (closure_mono _)
  rw [← Subtype.image_preimage_coe]
  -- ⊢ Subtype.val '' (Subtype.val ⁻¹' t) ⊆ Subtype.val '' closure (Subtype.val ⁻¹' …
  exact Set.image_subset _ subset_closure
  -- 🎉 no goals
#align quasi_sober_of_open_cover quasiSober_of_open_cover

/-- Any Hausdorff space is a quasi-sober space because any irreducible set is a singleton. -/
instance (priority := 100) T2Space.quasiSober [T2Space α] : QuasiSober α where
  sober h _ := by
    obtain ⟨x, rfl⟩ := isIrreducible_iff_singleton.mp h
    -- ⊢ ∃ x_1, IsGenericPoint x_1 {x}
    exact ⟨x, closure_singleton⟩
    -- 🎉 no goals
#align t2_space.quasi_sober T2Space.quasiSober

end Sober

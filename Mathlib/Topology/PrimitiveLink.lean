/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Topology.PrimitivePath

/-!
# Primitive links

This file defines `IsPrimitiveLink`: a set is a primitive link between two points if it is
the range of a primitive path with those endpoints.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X] {x y : X} {L S : Set X} {γ : Path x y}

open Set

/-- A set `L` is a primitive link from `x` to `y` if it is the image of a primitive path with
those endpoints. -/
def IsPrimitiveLink (L : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, γ.IsPrimitive ∧ range γ = L

open Function unitInterval

lemma Path.IsPrimitive.isPrimitiveLink (h : γ.IsPrimitive) : IsPrimitiveLink (range γ) x y :=
  ⟨γ, h, rfl⟩

lemma IsPrimitiveLink.of_injective (h : Injective γ) : IsPrimitiveLink (range γ) x y :=
  (Path.IsPrimitive.of_injective h).isPrimitiveLink

lemma IsPrimitiveLink.of_isSimpleLoop {γ : Path x x} (h : γ.IsSimpleLoop) :
    IsPrimitiveLink (range γ) x x :=
  h.isPrimitive.isPrimitiveLink

namespace IsPrimitiveLink

@[symm]
lemma symm (h : IsPrimitiveLink L x y) : IsPrimitiveLink L y x := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact ⟨γ.symm, hγ.symm, γ.symm_range⟩

lemma left_mem (h : IsPrimitiveLink L x y) : x ∈ L := by
  obtain ⟨γ, _, rfl⟩ := h
  exact γ.source_mem_range

lemma right_mem (h : IsPrimitiveLink L x y) : y ∈ L := h.symm.left_mem

lemma nonempty (h : IsPrimitiveLink L x y) : L.Nonempty := ⟨x, h.left_mem⟩

lemma isCompact (h : IsPrimitiveLink L x y) : IsCompact L := by
  obtain ⟨γ, _, rfl⟩ := h
  exact isCompact_range γ.continuous

lemma isPathConnected (h : IsPrimitiveLink L x y) : IsPathConnected L := by
  obtain ⟨γ, _, rfl⟩ := h
  exact γ.range_isPathConnected

lemma isConnected (h : IsPrimitiveLink L x y) : IsConnected L :=
  h.isPathConnected.isConnected

lemma image {Y : Type*} [TopologicalSpace Y] {f : X → Y} (h : IsPrimitiveLink L x y)
    (hf : ContinuousOn f L) (hinj : InjOn f L) : IsPrimitiveLink (f '' L) (f x) (f y) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact ⟨γ.map' hf, hγ.map hf hinj, range_comp f γ⟩

lemma diff_endpoints_nonempty (h : IsPrimitiveLink L x y) : (L \ {x, y}).Nonempty := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact hγ.range_diff_endpoints_nonempty

lemma isPathConnected_diff_endpoints (h : IsPrimitiveLink L x y) :
    IsPathConnected (L \ {x, y}) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  exact hγ.isPathConnected_range_diff_endpoints

lemma isConnected_diff_endpoints (h : IsPrimitiveLink L x y) : IsConnected (L \ {x, y}) :=
  h.isPathConnected_diff_endpoints.isConnected

/-- Every point of a primitive link is a limit of points other than its endpoints. -/
lemma subset_closure_diff_endpoints (h : IsPrimitiveLink L x y) : L ⊆ closure (L \ {x, y}) := by
  obtain ⟨γ, hγ, rfl⟩ := h
  rw [hγ.range_diff_endpoints]
  rintro _ ⟨t, rfl⟩
  refine image_closure_subset_closure_image γ.continuous ⟨t, ?_, rfl⟩
  rw [closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
  exact ⟨t.2.1, t.2.2⟩

/-- The endpoints belong to every closed set containing the link minus its endpoints. -/
lemma endpoints_mem_of_diff_subset (h : IsPrimitiveLink L x y) (hS : IsClosed S)
    (hsub : L \ {x, y} ⊆ S) : x ∈ S ∧ y ∈ S :=
  ⟨hS.closure_subset (closure_mono hsub (h.subset_closure_diff_endpoints h.left_mem)),
    hS.closure_subset (closure_mono hsub (h.subset_closure_diff_endpoints h.right_mem))⟩

end IsPrimitiveLink

lemma isPrimitiveLink_iff_exists_injective (hxy : x ≠ y) :
    IsPrimitiveLink L x y ↔ ∃ γ : Path x y, Injective γ ∧ range γ = L := by
  simp only [IsPrimitiveLink, Path.isPrimitive_iff_injective hxy]

lemma isPrimitiveLink_iff_exists_isSimpleLoop :
    IsPrimitiveLink L x x ↔ ∃ γ : Path x x, γ.IsSimpleLoop ∧ range γ = L := by
  simp only [IsPrimitiveLink, Path.isPrimitive_iff_isSimpleLoop]

/-
Copyright (c) 2023 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Intrinsic frontier and interior

This file defines the intrinsic frontier, interior and closure of a set in a normed additive torsor.
These are also known as relative frontier, interior, closure.

The intrinsic frontier/interior/closure of a set `s` is the frontier/interior/closure of `s`
considered as a set in its affine span.

The intrinsic interior is in general greater than the topological interior, the intrinsic frontier
in general less than the topological frontier, and the intrinsic closure in cases of interest the
same as the topological closure.

## Definitions

* `intrinsicInterior`: Intrinsic interior
* `intrinsicFrontier`: Intrinsic frontier
* `intrinsicClosure`: Intrinsic closure

## Results

The main results are:
* `AffineIsometry.image_intrinsicInterior`/`AffineIsometry.image_intrinsicFrontier`/
  `AffineIsometry.image_intrinsicClosure`: Intrinsic interiors/frontiers/closures commute with
  taking the image under an affine isometry.
* `Set.Nonempty.intrinsicInterior`: The intrinsic interior of a nonempty convex set is nonempty.

## References

* Chapter 8 of [Barry Simon, *Convexity*][simon2011]
* Chapter 1 of [Rolf Schneider, *Convex Bodies: The Brunn-Minkowski theory*][schneider2013].

## TODO

* `IsClosed s → IsExtreme 𝕜 s (intrinsicFrontier 𝕜 s)`
* `x ∈ s → y ∈ intrinsicInterior 𝕜 s → openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s`
-/

@[expose] public section

open AffineSubspace Set Topology
open scoped Pointwise

variable {𝕜 V W Q P : Type*}

section AddTorsor

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P]
  {s t : Set P} {x : P}

/-- The intrinsic interior of a set is its interior considered as a set in its affine span. -/
def intrinsicInterior (s : Set P) : Set P :=
  (↑) '' interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

/-- The intrinsic frontier of a set is its frontier considered as a set in its affine span. -/
def intrinsicFrontier (s : Set P) : Set P :=
  (↑) '' frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

/-- The intrinsic closure of a set is its closure considered as a set in its affine span. -/
def intrinsicClosure (s : Set P) : Set P :=
  (↑) '' closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)

variable {𝕜}

@[simp]
theorem mem_intrinsicInterior :
    x ∈ intrinsicInterior 𝕜 s ↔ ∃ y, y ∈ interior ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

@[simp]
theorem mem_intrinsicFrontier :
    x ∈ intrinsicFrontier 𝕜 s ↔ ∃ y, y ∈ frontier ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

@[simp]
theorem mem_intrinsicClosure :
    x ∈ intrinsicClosure 𝕜 s ↔ ∃ y, y ∈ closure ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s) ∧ ↑y = x :=
  mem_image _ _ _

theorem intrinsicInterior_subset : intrinsicInterior 𝕜 s ⊆ s :=
  image_subset_iff.2 interior_subset

theorem intrinsicFrontier_subset (hs : IsClosed s) : intrinsicFrontier 𝕜 s ⊆ s :=
  image_subset_iff.2 (hs.preimage continuous_induced_dom).frontier_subset

theorem intrinsicFrontier_subset_intrinsicClosure : intrinsicFrontier 𝕜 s ⊆ intrinsicClosure 𝕜 s :=
  image_mono frontier_subset_closure

theorem subset_intrinsicClosure : s ⊆ intrinsicClosure 𝕜 s :=
  fun x hx => ⟨⟨x, subset_affineSpan _ _ hx⟩, subset_closure hx, rfl⟩

@[simp]
theorem intrinsicInterior_empty : intrinsicInterior 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicInterior]

@[simp]
theorem intrinsicFrontier_empty : intrinsicFrontier 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicFrontier]

@[simp]
theorem intrinsicClosure_empty : intrinsicClosure 𝕜 (∅ : Set P) = ∅ := by simp [intrinsicClosure]

@[simp]
theorem intrinsicClosure_nonempty : (intrinsicClosure 𝕜 s).Nonempty ↔ s.Nonempty :=
  ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicClosure_empty,
    Nonempty.mono subset_intrinsicClosure⟩

alias ⟨Set.Nonempty.ofIntrinsicClosure, Set.Nonempty.intrinsicClosure⟩ := intrinsicClosure_nonempty

@[simp]
theorem intrinsicInterior_singleton (x : P) : intrinsicInterior 𝕜 ({x} : Set P) = {x} := by
  simp only [intrinsicInterior, preimage_coe_affineSpan_singleton, interior_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, setOf_eq_eq_singleton]

@[simp]
theorem intrinsicFrontier_singleton (x : P) : intrinsicFrontier 𝕜 ({x} : Set P) = ∅ := by
  rw [intrinsicFrontier, preimage_coe_affineSpan_singleton, frontier_univ, image_empty]

@[simp]
theorem intrinsicClosure_singleton (x : P) : intrinsicClosure 𝕜 ({x} : Set P) = {x} := by
  simp only [intrinsicClosure, preimage_coe_affineSpan_singleton, closure_univ, image_univ,
    Subtype.range_coe_subtype, mem_affineSpan_singleton, setOf_eq_eq_singleton]

/-!
Note that neither `intrinsicInterior` nor `intrinsicFrontier` is monotone.
-/


theorem intrinsicClosure_mono (h : s ⊆ t) : intrinsicClosure 𝕜 s ⊆ intrinsicClosure 𝕜 t := by
  refine image_subset_iff.2 fun x hx => ?_
  refine ⟨Set.inclusion (affineSpan_mono _ h) x, ?_, rfl⟩
  refine (continuous_inclusion (affineSpan_mono _ h)).closure_preimage_subset _ (closure_mono ?_ hx)
  exact fun y hy => h hy

theorem interior_subset_intrinsicInterior : interior s ⊆ intrinsicInterior 𝕜 s :=
  fun x hx => ⟨⟨x, subset_affineSpan _ _ <| interior_subset hx⟩,
    preimage_interior_subset_interior_preimage continuous_subtype_val hx, rfl⟩

theorem intrinsicClosure_subset_closure : intrinsicClosure 𝕜 s ⊆ closure s :=
  image_subset_iff.2 <| continuous_subtype_val.closure_preimage_subset _

theorem intrinsicFrontier_subset_frontier : intrinsicFrontier 𝕜 s ⊆ frontier s :=
  image_subset_iff.2 <| continuous_subtype_val.frontier_preimage_subset _

theorem intrinsicClosure_subset_affineSpan : intrinsicClosure 𝕜 s ⊆ affineSpan 𝕜 s :=
  (image_subset_range _ _).trans Subtype.range_coe.subset

@[simp]
theorem intrinsicClosure_diff_intrinsicFrontier (s : Set P) :
    intrinsicClosure 𝕜 s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s :=
  (image_diff Subtype.coe_injective _ _).symm.trans <| by
    rw [closure_diff_frontier, intrinsicInterior]

@[simp]
theorem intrinsicClosure_diff_intrinsicInterior (s : Set P) :
    intrinsicClosure 𝕜 s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s :=
  (image_diff Subtype.coe_injective _ _).symm

@[simp]
theorem intrinsicInterior_union_intrinsicFrontier (s : Set P) :
    intrinsicInterior 𝕜 s ∪ intrinsicFrontier 𝕜 s = intrinsicClosure 𝕜 s := by
  simp [intrinsicClosure, intrinsicInterior, intrinsicFrontier, closure_eq_interior_union_frontier,
    image_union]

@[simp]
theorem intrinsicFrontier_union_intrinsicInterior (s : Set P) :
    intrinsicFrontier 𝕜 s ∪ intrinsicInterior 𝕜 s = intrinsicClosure 𝕜 s := by
  rw [union_comm, intrinsicInterior_union_intrinsicFrontier]

theorem isClosed_intrinsicClosure (hs : IsClosed (affineSpan 𝕜 s : Set P)) :
    IsClosed (intrinsicClosure 𝕜 s) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure

theorem isClosed_intrinsicFrontier (hs : IsClosed (affineSpan 𝕜 s : Set P)) :
    IsClosed (intrinsicFrontier 𝕜 s) :=
  hs.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_frontier

@[simp]
theorem affineSpan_intrinsicClosure (s : Set P) :
    affineSpan 𝕜 (intrinsicClosure 𝕜 s) = affineSpan 𝕜 s :=
  (affineSpan_le.2 intrinsicClosure_subset_affineSpan).antisymm <|
    affineSpan_mono _ subset_intrinsicClosure

protected theorem IsClosed.intrinsicClosure (hs : IsClosed ((↑) ⁻¹' s : Set <| affineSpan 𝕜 s)) :
    intrinsicClosure 𝕜 s = s := by
  rw [intrinsicClosure, hs.closure_eq, image_preimage_eq_of_subset]
  exact (subset_affineSpan _ _).trans Subtype.range_coe.superset

@[simp]
theorem intrinsicClosure_idem (s : Set P) :
    intrinsicClosure 𝕜 (intrinsicClosure 𝕜 s) = intrinsicClosure 𝕜 s := by
  refine IsClosed.intrinsicClosure ?_
  set t := affineSpan 𝕜 (intrinsicClosure 𝕜 s) with ht
  clear_value t
  obtain rfl := ht.trans (affineSpan_intrinsicClosure _)
  rw [intrinsicClosure, preimage_image_eq _ Subtype.coe_injective]
  exact isClosed_closure

theorem intrinsicClosure_eq_closure_inter_affineSpan (s : Set P) :
    intrinsicClosure 𝕜 s = closure s ∩ affineSpan 𝕜 s := by
  have h : Topology.IsInducing ((↑) : affineSpan 𝕜 s → P) := .subtypeVal
  rw [intrinsicClosure, h.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range,
    Set.image_preimage_eq_of_subset ?_, Subtype.range_coe]
  rw [Subtype.range_coe]
  apply subset_affineSpan

@[simp]
theorem intrinsicInterior_prod_eq [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace Q]
    [AddTorsor W Q] (s : Set P) (t : Set Q) :
    intrinsicInterior 𝕜 (s ×ˢ t) = intrinsicInterior 𝕜 s ×ˢ intrinsicInterior 𝕜 t := by
  let e : affineSpan 𝕜 (s ×ˢ t) ≃ₜ affineSpan 𝕜 s × affineSpan 𝕜 t :=
    (Homeomorph.setCongr (coe_affineSpan_prod s t)).trans
      (Homeomorph.Set.prod (affineSpan 𝕜 s : Set P) (affineSpan 𝕜 t : Set Q))
  have himage : e '' ((↑) ⁻¹' (s ×ˢ t)) = ((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t) := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨z, hz, heq⟩; exact heq ▸ hz
    · intro h; exact ⟨e.symm (a, b), by simpa [e] using h, e.apply_symm_apply _⟩
  have hfst : ∀ x : affineSpan 𝕜 (s ×ˢ t), ((e x).1 : P) = (x : P × Q).1 := fun _ => rfl
  have hsnd : ∀ x : affineSpan 𝕜 (s ×ˢ t), ((e x).2 : Q) = (x : P × Q).2 := fun _ => rfl
  simp only [intrinsicInterior]; ext ⟨p1, p2⟩; simp only [mem_image, mem_prod]
  constructor
  · rintro ⟨x, hx, hx_eq⟩
    have hmem : e x ∈ interior (((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t)) := by
      rw [← himage, ← e.image_interior]; exact mem_image_of_mem e hx
    rw [interior_prod_eq] at hmem
    exact ⟨⟨(e x).1, hmem.1, by rw [hfst, hx_eq]⟩, ⟨(e x).2, hmem.2, by rw [hsnd, hx_eq]⟩⟩
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    have hab : (a, b) ∈ interior (((↑) ⁻¹' s) ×ˢ ((↑) ⁻¹' t)) := by
      rw [interior_prod_eq]; exact ⟨ha, hb⟩
    rw [← himage, ← e.image_interior] at hab
    obtain ⟨x, hx, hx_eq⟩ := hab
    exact ⟨x, hx, Prod.ext (by rw [← hfst]; exact congrArg (Subtype.val ∘ Prod.fst) hx_eq)
                             (by rw [← hsnd]; exact congrArg (Subtype.val ∘ Prod.snd) hx_eq)⟩
end AddTorsor

namespace AffineIsometry

variable [NormedField 𝕜] [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [NormedSpace 𝕜 V]
  [NormedSpace 𝕜 W] [MetricSpace P] [PseudoMetricSpace Q] [NormedAddTorsor V P]
  [NormedAddTorsor W Q]

@[simp]
theorem image_intrinsicInterior (φ : P →ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [intrinsicInterior_empty, image_empty]
  haveI : Nonempty s := hs.to_subtype
  let f := ((affineSpan 𝕜 s).isometryEquivMap φ).toHomeomorph
  have : φ.toAffineMap ∘ (↑) ∘ f.symm = (↑) := funext isometryEquivMap.apply_symm_apply
  rw [intrinsicInterior, intrinsicInterior, ← φ.coe_toAffineMap, ← map_span φ.toAffineMap s, ← this,
    ← Function.comp_assoc, image_comp, image_comp, f.symm.image_interior, f.image_symm,
    ← preimage_comp, Function.comp_assoc, f.symm_comp_self, AffineIsometry.coe_toAffineMap,
    Function.comp_id, preimage_comp, φ.injective.preimage_image]

@[simp]
theorem image_intrinsicFrontier (φ : P →ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicFrontier 𝕜 (φ '' s) = φ '' intrinsicFrontier 𝕜 s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  haveI : Nonempty s := hs.to_subtype
  let f := ((affineSpan 𝕜 s).isometryEquivMap φ).toHomeomorph
  have : φ.toAffineMap ∘ (↑) ∘ f.symm = (↑) := funext isometryEquivMap.apply_symm_apply
  rw [intrinsicFrontier, intrinsicFrontier, ← φ.coe_toAffineMap, ← map_span φ.toAffineMap s, ← this,
    ← Function.comp_assoc, image_comp, image_comp, f.symm.image_frontier, f.image_symm,
    ← preimage_comp, Function.comp_assoc, f.symm_comp_self, AffineIsometry.coe_toAffineMap,
    Function.comp_id, preimage_comp, φ.injective.preimage_image]

@[simp]
theorem image_intrinsicClosure (φ : P →ᵃⁱ[𝕜] Q) (s : Set P) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  haveI : Nonempty s := hs.to_subtype
  let f := ((affineSpan 𝕜 s).isometryEquivMap φ).toHomeomorph
  have : φ.toAffineMap ∘ (↑) ∘ f.symm = (↑) := funext isometryEquivMap.apply_symm_apply
  rw [intrinsicClosure, intrinsicClosure, ← φ.coe_toAffineMap, ← map_span φ.toAffineMap s, ← this,
    ← Function.comp_assoc, image_comp, image_comp, f.symm.image_closure, f.image_symm,
    ← preimage_comp, Function.comp_assoc, f.symm_comp_self, AffineIsometry.coe_toAffineMap,
    Function.comp_id, preimage_comp, φ.injective.preimage_image]

end AffineIsometry

section NormedAddTorsor

variable (𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [FiniteDimensional 𝕜 V] [MetricSpace P] [NormedAddTorsor V P] (s : Set P)

@[simp]
theorem intrinsicClosure_eq_closure : intrinsicClosure 𝕜 s = closure s := by
  ext x
  simp only [mem_closure_iff, mem_intrinsicClosure]
  refine ⟨?_, fun h => ⟨⟨x, _⟩, ?_, Subtype.coe_mk _ ?_⟩⟩
  · rintro ⟨x, h, rfl⟩ t ht hx
    obtain ⟨z, hz₁, hz₂⟩ := h _ (continuous_induced_dom.isOpen_preimage t ht) hx
    exact ⟨z, hz₁, hz₂⟩
  · rintro _ ⟨t, ht, rfl⟩ hx
    obtain ⟨y, hyt, hys⟩ := h _ ht hx
    exact ⟨⟨_, subset_affineSpan 𝕜 s hys⟩, hyt, hys⟩
  · by_contra hc
    obtain ⟨z, hz₁, hz₂⟩ := h _ (affineSpan 𝕜 s).closed_of_finiteDimensional.isOpen_compl hc
    exact hz₁ (subset_affineSpan 𝕜 s hz₂)

variable {𝕜}

@[simp]
theorem closure_diff_intrinsicInterior (s : Set P) :
    closure s \ intrinsicInterior 𝕜 s = intrinsicFrontier 𝕜 s :=
  intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_diff_intrinsicInterior s

@[simp]
theorem closure_diff_intrinsicFrontier (s : Set P) :
    closure s \ intrinsicFrontier 𝕜 s = intrinsicInterior 𝕜 s :=
  intrinsicClosure_eq_closure 𝕜 s ▸ intrinsicClosure_diff_intrinsicFrontier s

end NormedAddTorsor

section Convex

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul 𝕜 V] {s : Set V}

protected theorem Convex.intrinsicClosure (hs : Convex 𝕜 s) : Convex 𝕜 (intrinsicClosure 𝕜 s) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact hs.closure.inter (affineSpan 𝕜 s).convex

end Convex

private theorem aux {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (φ : α ≃ₜ β)
    (s : Set β) : (interior s).Nonempty ↔ (interior (φ ⁻¹' s)).Nonempty := by
  rw [← φ.image_symm, ← φ.symm.image_interior, image_nonempty]

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {s : Set V}

/-- The intrinsic interior of a nonempty convex set is nonempty. -/
protected theorem Set.Nonempty.intrinsicInterior (hscv : Convex ℝ s) (hsne : s.Nonempty) :
    (intrinsicInterior ℝ s).Nonempty := by
  haveI := hsne.coe_sort
  obtain ⟨p, hp⟩ := hsne
  let p' : _root_.affineSpan ℝ s := ⟨p, subset_affineSpan _ _ hp⟩
  rw [intrinsicInterior, image_nonempty,
    aux (AffineIsometryEquiv.constVSub ℝ p').symm.toHomeomorph,
    Convex.interior_nonempty_iff_affineSpan_eq_top, AffineIsometryEquiv.coe_toHomeomorph, ←
    AffineIsometryEquiv.coe_toAffineEquiv, ← comap_span, affineSpan_coe_preimage_eq_top, comap_top]
  exact hscv.affine_preimage
    ((_root_.affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ p').symm.toAffineEquiv.toAffineMap)

theorem intrinsicInterior_nonempty (hs : Convex ℝ s) :
    (intrinsicInterior ℝ s).Nonempty ↔ s.Nonempty :=
  ⟨by simp_rw [nonempty_iff_ne_empty]; rintro h rfl; exact h intrinsicInterior_empty,
    Set.Nonempty.intrinsicInterior hs⟩

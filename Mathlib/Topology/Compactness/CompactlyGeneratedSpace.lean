/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Topology.Category.CompactlyGenerated
import Mathlib.Topology.Compactification.OnePoint

/-!
# Compactly generated topological spaces

This file defines compactly generated topological spaces as a special case of
`UCompactlyGeneratedSpaces`. A compactly generated space is a space such that a set `s` is closed
if and only if for all compact Hausdorff space `K` and `f : K → X` continuous, `f ⁻¹' s` is closed
in `K`. The typeclass `CompactlyGeneratedSpace` is defined by taking `K : Type u` when `X : Type u`,
contrary to `UCompactlyGeneratedSpace` where spaces `K` can be taken in another universe.

We prov basic properties and instances, and prove that a `SequentialSpace` is compactly generated,
as well as Hausdorff `WeaklyLocallyCompactSpace`.

## Main definitions

* `CompactlyGeneratedSpace X`: the topology of `X` is coinduced by continuous maps coming from
  compact Hausdorff spaces.

## References

* <https://en.wikipedia.org/wiki/Compactly_generated_space>
* <https://ncatlab.org/nlab/files/StricklandCGHWSpaces.pdf>

## Tags

compactly generated space
-/

universe u v

open TopologicalSpace Filter Topology Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A topological space `X : Type u` is compactly generated if its topology is coinduced by
continuous maps `f : K → X`, where `K : Type u` is compact Hausdorff. -/
abbrev CompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop :=
  UCompactlyGeneratedSpace.{u} X

/-- A topological space `X` is compactly generated if a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem compactlyGeneratedSpace_of_isClosed
    (h : ∀ (s : Set X), (∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) → IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine uCompactlyGeneratedSpace_of_continuous_maps fun f h' ↦
    continuous_iff_isClosed.2 fun t ht ↦ h _ ?_
  intro K _ _ _ g hg
  exact ht.preimage (h' (CompHaus.of K) { toFun := g, continuous_toFun := hg })

/-- A topological space `X` is compactly generated if a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem compactlyGeneratedSpace_of_isOpen
    (h : ∀ (s : Set X), (∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) → IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s h' ↦ isOpen_compl_iff.1 <| h _ fun f hf ↦ ?_
  rw [preimage_compl, isOpen_compl_iff]
  exact h' f hf

/-- In a compactly generated space `X`, a set `s` is closed when `f ⁻¹' s` is
closed for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem CompactlyGeneratedSpace.isClosed' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) : IsClosed s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
    isClosed_sigma_iff]
  exact fun ⟨_, f⟩ ↦ hs f f.continuous

/-- In a compactly generated space `X`, a set `s` is closed when `s ∩ K` is
closed for every compact `K ⊆ X`. -/
theorem CompactlyGeneratedSpace.isClosed [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K)) : IsClosed s := by
  refine isClosed' fun f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/-- In a compactly generated space `X`, a set `s` is open when `f ⁻¹' s` is
open for every continuous map `f : K → X`, where `K` is compact Hausdorff. -/
theorem CompactlyGeneratedSpace.isOpen' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) : IsOpen s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isOpen_coinduced,
    isOpen_sigma_iff]
  exact fun ⟨_, f⟩ ↦ hs f f.continuous

/-- In a compactly generated space `X`, a set `s` is closed when `s ∩ K` is
closed for every compact `K ⊆ X`. -/
theorem CompactlyGeneratedSpace.isOpen [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsOpen (s ∩ K)) : IsOpen s := by
  refine isOpen' fun f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

/-- If the topology of `X` is coinduced by a continuous function whose domain is
compactly generated, then so is `X`. -/
theorem compactlyGeneratedSpace_of_coinduced {Y : Type u}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    CompactlyGeneratedSpace Y := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ ?_
  rw [ht, isClosed_coinduced]
  refine CompactlyGeneratedSpace.isClosed' fun g hg ↦ h _ (hf.comp hg)

/-- The quotient of a compactly generated space is compactly generated. -/
instance {S : Setoid X} [CompactlyGeneratedSpace X] : CompactlyGeneratedSpace (Quotient S) :=
  compactlyGeneratedSpace_of_coinduced continuous_quotient_mk' rfl

/-- The sum of two compactly generated spaces is compactly generated. -/
instance [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    CompactlyGeneratedSpace (X ⊕ Y) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine CompactlyGeneratedSpace.isClosed' ?_
    intro K _ _ _ f hf
  · let g : ULift.{v} K → X ⊕ Y := Sum.inl ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inl.comp <| hf.comp continuous_uLift_down
    exact (h g hg).preimage continuous_uLift_up
  · let g : ULift.{u} K → X ⊕ Y := Sum.inr ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inr.comp <| hf.comp continuous_uLift_down
    exact (h g hg).preimage continuous_uLift_up


instance {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactlyGeneratedSpace (X i)] : CompactlyGeneratedSpace (Σ i, X i) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sigma_iff.2 fun i ↦
    CompactlyGeneratedSpace.isClosed' ?_
  intro K _ _ _ f hf
  let g : ULift.{u} K → Σ i, X i := Sigma.mk i ∘ f ∘ ULift.down
  have hg : Continuous g := continuous_sigmaMk.comp <| hf.comp continuous_uLift_down
  exact (h g hg).preimage continuous_uLift_up

open OnePoint in
instance (priority := 100) [SequentialSpace X] : CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦
    SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_
  let g : ULift.{u} (OnePoint ℕ) → X := (continuousMapMkNat u p hup) ∘ ULift.down
  change ULift.up ∞ ∈ g ⁻¹' s
  have : Filter.Tendsto (@OnePoint.some ℕ) Filter.atTop (𝓝 ∞) := by
    rw [← Nat.cofinite_eq_atTop, ← cocompact_eq_cofinite, ← coclosedCompact_eq_cocompact]
    exact tendsto_coe_infty
  apply IsClosed.mem_of_tendsto _ ((continuous_uLift_up.tendsto ∞).comp this)
  · simp only [Function.comp_apply, mem_preimage, eventually_atTop, ge_iff_le]
    exact ⟨0, fun b _ ↦ hu b⟩
  · exact h g ((continuousMapMkNat u p hup).continuous.comp continuous_uLift_down)

theorem compactlyGeneratedSpace_of_isClosed_of_t2 [T2Space X]
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) → IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs ↦ h s fun K hK ↦ ?_
  rw [Set.inter_comm, ← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs Subtype.val continuous_subtype_val

theorem compactlyGeneratedSpace_of_isOpen_of_t2 [T2Space X]
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsOpen ((Subtype.val) ⁻¹' s : Set ↑K)) → IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs ↦ h s fun K hK ↦ ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs Subtype.val continuous_subtype_val

instance (priority := 100) [WeaklyLocallyCompactSpace X] [T2Space X] :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun s h ↦ ?_
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃

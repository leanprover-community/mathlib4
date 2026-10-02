/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.ShrinkingLemma

/-! # Closed swellings of finite covers -/

public section

open Set TopologicalSpace

universe u v

/-- Preservation of nonempty finite intersections transfers an
indexwise multiplicity bound from a source family to the range of a target family. -/
lemma hasOrderLE_of_finiteIntersection_preserving
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {q : ℕ}
    (K E : ι → Set X)
    (hKorder : ∀ x : X, Set.encard {i | x ∈ K i} ≤ q)
    (hnerve : ∀ s : Finset ι,
      (⋂ i ∈ s, closure (E i)).Nonempty → (⋂ i ∈ s, K i).Nonempty) :
    (Set.range E).HasOrderLE q := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  -- At a point of the target family, collect the finitely many incident indices.
  rw [Set.hasOrderLE_iff]
  intro x
  let s : Finset ι := Finset.univ.filter fun i ↦ x ∈ E i
  obtain ⟨y, hy⟩ := hnerve s
    ⟨x, Set.mem_iInter₂.mpr fun i hi ↦ subset_closure (Finset.mem_filter.mp hi).2⟩
  -- Distinct incident target sets are images of incident indices, all of which meet at `y` in
  -- the source family.
  change ((Set.range E) ∩ {U | x ∈ U}).encard ≤ q
  rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  refine (Set.encard_image_le _ _).trans ((Set.encard_mono ?_).trans (hKorder y))
  change ∀ i, x ∈ E i → y ∈ K i
  simpa only [Set.mem_iInter, s, Finset.mem_filter, Finset.mem_univ, true_and] using hy

/-- An order-bounded finite cover of a closed subtype, together with
a closure-controlled shrinking, swells to an ambient open family with the same order bound. -/
lemma existsAmbientOpenSwelling_of_closedSubtypeCover
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
    {L : Set X} (hL : IsClosed L) {ι : Type v} [Finite ι] {q : ℕ}
    {B C : ι → Opens L} (hCcover : IsOpenCover C)
    (hBorder : (Set.range fun i ↦ (B i : Set L)).HasOrderLE q)
    (hBinjective : Function.Injective fun i ↦ (B i : Set L))
    (hCclosure : ∀ i, closure (C i : Set L) ⊆ B i)
    (A : ι → Opens X) (hBA : ∀ i, Subtype.val '' (B i : Set L) ⊆ A i) :
    ∃ E : ι → Opens X, L ⊆ ⋃ i, (E i : Set X) ∧ (∀ i, closure (E i : Set X) ⊆ A i) ∧
      (Set.range fun i ↦ (E i : Set X)).HasOrderLE q := by
  classical
  let K : ι → Set X := fun i ↦ Subtype.val '' closure (C i : Set L)
  have hKclosed : ∀ i, IsClosed (K i) :=
    fun i ↦ hL.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure
  have hKA : ∀ i, K i ⊆ A i :=
    fun i ↦ (Set.image_mono (hCclosure i)).trans (hBA i)
  obtain ⟨E, hKE, hEclosure, hnerveEmpty⟩ :=
    existsOpenSwelling_preservingFiniteIntersections hKclosed hKA
  have hKorder : ∀ x : X, Set.encard {i | x ∈ K i} ≤ q := by
    intro x
    by_cases hx : {i | x ∈ K i}.Nonempty
    · obtain ⟨i, zi, hzi, rfl⟩ := hx
      refine (Set.encard_le_encard_of_injOn (f := fun j ↦ (B j : Set L))
        ?_ hBinjective.injOn).trans (Set.hasOrderLE_iff.mp hBorder zi)
      intro j hj
      exact ⟨Set.mem_range_self j, hCclosure j (by simpa [K] using hj)⟩
    · simp [Set.not_nonempty_iff_eq_empty.mp hx]
  have hEorder : (Set.range fun i ↦ (E i : Set X)).HasOrderLE q := by
    apply hasOrderLE_of_finiteIntersection_preserving K (fun i ↦ (E i : Set X)) hKorder
    intro s
    simpa only [Set.nonempty_iff_ne_empty] using mt (hnerveEmpty s)
  refine ⟨E, ?_, hEclosure, hEorder⟩
  -- The closed seeds contain the original shrinking, so their swellings cover the closed locus.
  intro x hxL
  let z : L := ⟨x, hxL⟩
  obtain ⟨i, hzi⟩ := hCcover.exists_mem z
  exact Set.mem_iUnion.mpr ⟨i, hKE i ⟨z, subset_closure hzi, rfl⟩⟩

end

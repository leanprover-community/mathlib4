/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Convenient.GeneratedBy
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds

/-!
# Open or closed subsets that are also `X`-generated spaces

Let `X : ι → Type*` be a family of topological spaces.
If all the opens (resp. closed) subsets of the `X i` are
`X`-generated, then any open (resp. closed) subset of
an `X`-generated space is `X`-generated.

-/

public section

open Topology

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  {Y : Type*} [TopologicalSpace Y]

section

variable [∀ (i : ι) (U : TopologicalSpace.Opens (X i)), IsGeneratedBy X U]

lemma IsOpen.isGeneratedBy [IsGeneratedBy X Y] {U : Set Y} (hU : IsOpen U) :
    IsGeneratedBy X U := by
  let W (a : Σ (i : ι), C(X i, Y)) : TopologicalSpace.Opens (X a.1) :=
    ⟨a.2 ⁻¹' U, a.2.continuous.isOpen_preimage U hU⟩
  let g (a) : W a → U := U.restrictPreimage a.2
  have hg (a) : Continuous (g a) := a.2.continuous.restrictPreimage
  suffices ∀ (V : Set U), (∀ a, IsOpen ((g a) ⁻¹' V)) → IsOpen V by
    constructor
    rw [continuous_def]
    exact fun _ hV ↦ this _ (fun a ↦
      ((IsGeneratedBy.equiv_symm_comp_continuous_iff X _).2 (hg a)).isOpen_preimage _ hV)
  intro V hV
  obtain ⟨V, hV, rfl⟩ : ∃ (T : Set Y), T ⊆ U ∧ V = Subtype.val ⁻¹' T :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine continuous_subtype_val.isOpen_preimage _ ?_
  rw [IsGeneratedBy.isOpen_iff X]
  intro i f
  convert (W ⟨i, f⟩).isOpen.isOpenMap_subtype_val _ (hV ⟨i, f⟩)
  aesop

lemma Topology.IsOpenEmbedding.isGeneratedBy [IsGeneratedBy X Y]
    {F : Type*} [TopologicalSpace F] {f : F → Y}
    (hf : IsOpenEmbedding f) :
    IsGeneratedBy X F :=
  have := hf.isOpen_range.isGeneratedBy (X := X)
  hf.toIsEmbedding.toHomeomorph.symm.isQuotientMap.isGeneratedBy

end

section

variable [∀ (i : ι) (F : TopologicalSpace.Closeds (X i)), IsGeneratedBy X F]

lemma IsClosed.isGeneratedBy [IsGeneratedBy X Y] {F : Set Y} (hF : IsClosed F) :
    IsGeneratedBy X F := by
  let W (a : Σ (i : ι), C(X i, Y)) : TopologicalSpace.Closeds (X a.1) :=
    ⟨a.2 ⁻¹' F, IsClosed.preimage a.2.continuous hF⟩
  let g (a) : W a → F := F.restrictPreimage a.2
  have hg (a) : Continuous (g a) := a.2.continuous.restrictPreimage
  suffices ∀ (V : Set F), (∀ a, IsClosed ((g a) ⁻¹' V)) → IsClosed V by
    constructor
    rw [continuous_iff_isClosed]
    exact fun _ hV ↦ this _ (fun a ↦ IsClosed.preimage
      ((IsGeneratedBy.equiv_symm_comp_continuous_iff X _).2 (hg a)) hV)
  intro V hV
  obtain ⟨V, hV, rfl⟩ : ∃ (T : Set Y), T ⊆ F ∧ V = Subtype.val ⁻¹' T :=
    ⟨Subtype.val '' V, by simp, by simp⟩
  refine IsClosed.preimage continuous_subtype_val ?_
  rw [IsGeneratedBy.isClosed_iff X]
  intro i f
  convert (W ⟨i, f⟩).isClosed.isClosedMap_subtype_val _ (hV ⟨i, f⟩)
  aesop

lemma Topology.IsClosedEmbedding.isGeneratedBy [IsGeneratedBy X Y]
    {U : Type*} [TopologicalSpace U] {f : U → Y}
    (hf : IsClosedEmbedding f) :
    IsGeneratedBy X U :=
  have := hf.isClosed_range.isGeneratedBy (X := X)
  hf.toIsEmbedding.toHomeomorph.symm.isQuotientMap.isGeneratedBy

end

/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Open covers

We define `IsOpenCover` as a predicate on indexed families of open sets in a topological space `X`,
asserting that their union is `X`. This is an example of a declaration whose name is actually
longer than its content; but giving it a name serves as a way of standardizing API.
-/

@[expose] public section

open Set Topology

namespace TopologicalSpace

/-- An indexed family of open sets whose union is `X`. -/
def IsOpenCover {ι X : Type*} [TopologicalSpace X] (u : ι → Opens X) : Prop :=
  iSup u = ⊤

variable {ι κ X Y : Type*} [TopologicalSpace X] {u : ι → Opens X}
  [TopologicalSpace Y] {v : κ → Opens Y}

namespace IsOpenCover

lemma mk (h : iSup u = ⊤) : IsOpenCover u := h

lemma of_sets {v : ι → Set X} (h_open : ∀ i, IsOpen (v i)) (h_iUnion : ⋃ i, v i = univ) :
    IsOpenCover (fun i ↦ ⟨v i, h_open i⟩) := by
  simp [IsOpenCover, h_iUnion]

lemma iSup_eq_top (hu : IsOpenCover u) : ⨆ i, u i = ⊤ := hu

lemma iSup_set_eq_univ (hu : IsOpenCover u) : ⋃ i, (u i : Set X) = univ := by
  simpa [← SetLike.coe_set_eq] using hu.iSup_eq_top

/-- Pullback of a covering of `Y` by a continuous map `X → Y`, giving a covering of `X` with the
same index type. -/
lemma comap (hv : IsOpenCover v) (f : C(X, Y)) : IsOpenCover fun k ↦ (v k).comap f :=
  by simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]

lemma exists_mem (hu : IsOpenCover u) (a : X) : ∃ i, a ∈ u i := by
  simpa [← hu.iSup_set_eq_univ] using mem_univ a

lemma exists_mem_nhds (hu : IsOpenCover u) (a : X) : ∃ i, (u i : Set X) ∈ 𝓝 a :=
  match hu.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩

lemma iUnion_inter (hu : IsOpenCover u) (s : Set X) :
    ⋃ i, s ∩ u i = s := by
  simp [← inter_iUnion, hu.iSup_set_eq_univ]

lemma isTopologicalBasis (hu : IsOpenCover u)
    {B : ∀ i, Set (Set (u i))} (hB : ∀ i, IsTopologicalBasis (B i)) :
    IsTopologicalBasis (⋃ i, (Subtype.val '' ·) '' B i) :=
  isTopologicalBasis_of_cover (fun i ↦ (u i).2) hu.iSup_set_eq_univ hB

end IsOpenCover

section IrreducibleSpace

open Function

/-- Irreducibility can be checked on an open cover with pairwise non-empty intersections. -/
theorem IrreducibleSpace.of_openCover {X ι : Type*} [TopologicalSpace X] [hι : Nonempty ι]
    {U : ι → TopologicalSpace.Opens X} (hU : TopologicalSpace.IsOpenCover U)
    (hn : Pairwise ((¬ Disjoint · ·) on U))
    (h : ∀ i, IrreducibleSpace ↥(U i)) :
    IrreducibleSpace X := by
  have h' (i : _) : IsIrreducible (U i).carrier :=
    IsIrreducible.of_subtype _
  let i : ι := Classical.choice (α := ι) hι
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier (h' i)
    with ⟨u, hu, hUu⟩
  by_cases huniv : u = Set.univ
  · rw [huniv] at hu
    exact (irreducibleSpace_def _).mpr hu.1
  · have huo : IsOpen uᶜ :=
      IsClosed.isOpen_compl (self := isClosed_of_mem_irreducibleComponents u hu)
    push_neg at huniv
    rw [u.ne_univ_iff_exists_notMem] at huniv
    choose a ha using huniv
    choose j haj using hU.exists_mem a
    have hji : j ≠ i := fun hji' ↦ ha <| hUu <| hji' ▸ haj
    rcases Set.inter_nonempty_iff_exists_left.mp
      ((h' j).2 (U i) uᶜ (U i).isOpen huo
      (not_disjoint_iff_nonempty_inter.mp (by simpa using hn hji)) ⟨a, ⟨haj, ha⟩⟩).right
      with ⟨x, hx₁, hx₂⟩
    exfalso; exact hx₂ <| hUu hx₁

end IrreducibleSpace

end TopologicalSpace

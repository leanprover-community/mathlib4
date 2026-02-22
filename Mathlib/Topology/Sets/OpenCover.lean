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
lemma comap (hv : IsOpenCover v) (f : C(X, Y)) : IsOpenCover fun k ↦ (v k).comap f := by
  simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]

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

set_option backward.isDefEq.respectTransparency false in
lemma Opens.IsBasis.isOpenCover {S : Set (Opens X)} (hS : Opens.IsBasis S) :
    IsOpenCover (fun U : S ↦ (U : Opens X)) :=
  top_le_iff.mp (subset_trans hS.2.superset (by simp))

set_option backward.isDefEq.respectTransparency false in
/-- Given an open cover and a basis,
the set of basis elements contained in any of the covers is still a cover. -/
lemma Opens.IsBasis.isOpenCover_mem_and_le {S : Set (Opens X)} (hS : Opens.IsBasis S)
    {U : ι → Opens X} (hU : IsOpenCover U) :
    IsOpenCover (fun V : { x : Opens X × ι // x.1 ∈ S ∧ x.1 ≤ U x.2 } ↦ V.1.1) := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hS.exists_subset_of_mem_open hxi (U i).2
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨⟨(V, i), hV, hVU⟩, hxV⟩

end TopologicalSpace

section Irreducible

open TopologicalSpace Function

set_option backward.isDefEq.respectTransparency false in
/-- (Pre)Irreducibility of an open set can be checked on a cover by opens
with pairwise non-empty intersections. -/
theorem IsPreirreducible.of_subset_iUnion {X ι : Type*} [TopologicalSpace X]
    {U : ι → Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U))
    (h : ∀ i, IsPreirreducible ((U i) : Set X))
    {s : Set X} (hs : IsOpen s) (hsU : s ⊆ ⋃ i, U i) :
    IsPreirreducible s := by
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he]; exact isPreirreducible_empty
  · choose x hx using hne
    choose i hi using mem_iUnion.mp <| hsU hx
    rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier ⟨⟨x, hi⟩, h i⟩
      with ⟨u, hu, hUu⟩
    by_cases huniv : s ⊆ u
    · exact hu.1.2.open_subset hs huniv
    · have huo : IsOpen uᶜ :=
        IsClosed.isOpen_compl (self := isClosed_of_mem_irreducibleComponents u hu)
      rcases not_subset.mp huniv with ⟨a, ⟨ha₁, ha₂⟩⟩
      choose j haj using mem_iUnion.mp <| hsU ha₁
      have hji : j ≠ i := fun hji' ↦ ha₂ <| hUu <| hji' ▸ haj
      rcases inter_nonempty_iff_exists_left.mp
        ((h j) (U i) uᶜ (U i).isOpen huo
        (not_disjoint_iff_nonempty_inter.mp (by simpa using hn hji)) ⟨a, ⟨haj, ha₂⟩⟩).right
        with ⟨x, hx₁, hx₂⟩
      exfalso; exact hx₂ <| hUu hx₁

set_option backward.isDefEq.respectTransparency false in
/-- (Pre)Irreducibility can be checked on an open cover with pairwise non-empty intersections. -/
theorem PreirreducibleSpace.of_isOpenCover {X ι : Type*} [TopologicalSpace X]
    {U : ι → Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U)) (hU : IsOpenCover U)
    (h : ∀ i, PreirreducibleSpace (U i)) :
    PreirreducibleSpace X :=
  have h' (i : _) : IsPreirreducible (U i).carrier := IsPreirreducible.of_subtype
  ⟨IsPreirreducible.of_subset_iUnion hn h' isOpen_univ (by simpa using hU.iSup_set_eq_univ)⟩

end Irreducible

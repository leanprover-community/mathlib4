/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz, Robert Maxton
-/

import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Subcomplexes

In this file we discuss subcomplexes of CW complexes.
The definintion of subcomplexes is in the file `Topology.CWComplex.Classical.Basic`.

## Main results
* `RelCWComplex.Subcomplex.instRelCWComplex`: a subcomplex of a (relative) CW complex is again a
  (relative) CW complex.

## References
* [K. Jänich, *Topology*][Janich1984]
-/

noncomputable section

open Metric Set Set.Notation

namespace Topology

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

lemma RelCWComplex.Subcomplex.closedCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    closedCell n i ⊆ E := by
  rw [← closure_openCell_eq_closedCell, E.closed.closure_subset_iff, ← E.union]
  apply subset_union_of_subset_right
  exact subset_iUnion_of_subset n
    (subset_iUnion (fun (j : ↑(E.I n)) ↦ openCell (C := C) n j) ⟨i, hi⟩)

lemma RelCWComplex.Subcomplex.openCell_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    openCell n i ⊆ E :=
  (openCell_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

lemma RelCWComplex.Subcomplex.cellFrontier_subset_of_mem [T2Space X] [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (hi : i ∈ E.I n) :
    cellFrontier n i ⊆ E :=
  (cellFrontier_subset_closedCell n i).trans (closedCell_subset_of_mem E hi)

/-- A subcomplex is the union of its closed cells and its base. -/
lemma RelCWComplex.Subcomplex.union_closedCell [T2Space X] [RelCWComplex C D] (E : Subcomplex C) :
    D ∪ ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E := by
  apply subset_antisymm
  · apply union_subset E.base_subset
    exact iUnion₂_subset fun n i ↦ closedCell_subset_of_mem E i.2
  · rw [← E.union]
    apply union_subset_union_right
    apply iUnion₂_mono fun n i ↦ ?_
    exact openCell_subset_closedCell (C := C) n i

/-- A subcomplex is the union of its closed cells. -/
lemma CWComplex.Subcomplex.union_closedCell [T2Space X] [CWComplex C] (E : Subcomplex C) :
    ⋃ (n : ℕ) (j : E.I n), closedCell (C := C) n j = E :=
  (empty_union _ ).symm.trans (RelCWComplex.Subcomplex.union_closedCell E)

lemma RelCWComplex.Subcomplex.disjoint_openCell_subcomplex_of_not_mem [RelCWComplex C D]
    (E : Subcomplex C) {n : ℕ} {i : cell C n} (h : i ∉ E.I n) : Disjoint (openCell n i) E := by
  simp_rw [← union, disjoint_union_right, disjoint_iUnion_right]
  exact ⟨disjointBase n i , fun _ _ ↦ disjoint_openCell_of_ne (by aesop)⟩

lemma RelCWComplex.Subcomplex.cell_mem_of_mem [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    {n} {i : cell C n} {x} (hxE : x ∈ E) (hxo : x ∈ openCell n i) : i ∈ E.I n := by
  by_contra! h!
  exact disjoint_openCell_subcomplex_of_not_mem E h! |>.notMem_of_mem_left hxo hxE

open Classical in
/-- A subcomplex is again a CW complex. -/
@[simps]
instance RelCWComplex.Subcomplex.toComplex [T2Space X] [𝓔 : RelCWComplex C D]
    (E : Subcomplex C) : RelCWComplex E D where
  cell n := E.I n
  map n i := map (C := C) n i
  source_eq n i := source_eq (C := C) n i
  continuousOn n i := continuousOn (C := C) n i
  continuousOn_symm n i := continuousOn_symm (C := C) n i
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    refine @pairwiseDisjoint' _ _ C D _ ⟨n, i⟩ trivial ⟨m, j⟩ trivial ?_
    exact Function.injective_id.sigma_map (fun _ ↦ Subtype.val_injective) |>.ne hne
  disjointBase' n i := disjointBase' (C := C) n i
  mapsTo := by
    intro n i
    rcases cellFrontier_subset_finite_openCell (C := C) n i with ⟨J, hJ⟩
    use fun m ↦ Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp_rw [iUnion_coe_set, mem_union, mem_iUnion, Finset.mem_preimage, exists_prop,
      Decidable.or_iff_not_imp_left] at hJ ⊢
    intro h
    specialize hJ h
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    suffices j ∈ E.I m from ⟨m, hmn, j, this, hj, openCell_subset_closedCell _ _ hxj⟩
    have : x ∈ (E : Set X) := E.cellFrontier_subset_of_mem i.2 hx
    by_contra hj'
    exact E.disjoint_openCell_subcomplex_of_not_mem hj' |>.notMem_of_mem_left hxj this
  closed' A hA h := by
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (subset_trans hA (subset_complex (C := C) E)) h.2
    intro n _ j
    by_cases hj : j ∈ E.I n
    · exact Or.intro_right _ (h.1 n ⟨j, hj⟩)
    · exact Or.intro_left _ ((disjoint_openCell_subcomplex_of_not_mem E hj).symm.mono_left hA)
  isClosedBase := isClosedBase (C := C)
  union' := union_closedCell E

/-- A subcomplex is again a CW complex. -/
instance CWComplex.Subcomplex.instCWComplex [T2Space X] [CWComplex C] (E : Subcomplex C) :
    CWComplex (E : Set X) :=
  RelCWComplex.toCWComplex (E : Set X)

@[simp]
lemma CWComplex.Subcomplex.cell_def [T2Space X] [CWComplex C] (E : Subcomplex C)
    (n : ℕ) : cell (E : Set X) n = E.I (C := C) n :=
  rfl

@[simp]
lemma CWComplex.Subcomplex.map_def [T2Space X] [CWComplex C] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : map (C := E) n i = map (C := C) n i :=
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.openCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C) (n : ℕ)
    (i : E.I n) : openCell (C := E) n i = openCell n (i : cell C n) := by
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.closedCell_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : ℕ) (i : E.I n) : closedCell (C := E) n i = closedCell n (i : cell C n) := by
  rfl

@[simp]
lemma RelCWComplex.Subcomplex.cellFrontier_eq [T2Space X] [RelCWComplex C D] (E : Subcomplex C)
    (n : ℕ) (i : E.I n) : cellFrontier (C := E) n i = cellFrontier n (i : cell C n) := by
  rfl

instance RelCWComplex.Subcomplex.finiteType_subcomplex_of_finiteType [T2Space X]
    [RelCWComplex C D] [FiniteType C] (E : Subcomplex C) : FiniteType (E : Set X) where
  finite_cell n :=
    let _ := FiniteType.finite_cell (C := C) (D := D) n
    Subtype.finite

instance RelCWComplex.Subcomplex.finiteDimensional_subcomplex_of_finiteDimensional
    [T2Space X] [RelCWComplex C D] [FiniteDimensional C] (E : Subcomplex C) :
    FiniteDimensional (E : Set X) where
  eventually_isEmpty_cell := by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    simp [isEmpty_subtype]

/-- A subcomplex of a finite CW complex is again finite. -/
instance RelCWComplex.Subcomplex.finite_subcomplex_of_finite [T2Space X] [RelCWComplex C D]
    [Finite C] (E : Subcomplex C) : Finite (E : Set X) :=
  finite_of_finiteDimensional_finiteType _

/-- A CW complex is coherent with any collection of subcomplexes that span the complex. -/
lemma RelCWComplex.Subcomplex.isCoherentWith_cover [T2Space X] [𝓔 : RelCWComplex C D]
    {ι} (𝒮 : ι → Subcomplex C) (h𝒮 : C ⊆ ⋃ i, 𝒮 i) :
    IsCoherentWith (range (C ↓∩ 𝒮 ·)) := by
  rcases em (Nonempty ι) with ⟨⟨i⟩⟩ | hι₀
  · apply 𝓔.isCoherentWith_closedCells.enlarge
    simp only [mem_insert_iff, mem_range, Sigma.exists, exists_exists_eq_and, forall_eq_or_imp,
      forall_exists_index]
    split_ands
    · use i, preimage_mono (𝒮 i).base_subset
    · rintro _ n j rfl
      have := target_eq n j ▸ (map n j).map_source (show 0 ∈ (map n j).source by simp [source_eq])
      obtain ⟨_, ⟨⟨i, rfl⟩, hi₀⟩⟩ := h𝒮 (openCell_subset_complex n j this)
      replace hi₀ := (𝒮 i).cell_mem_of_mem hi₀ this
      use i, preimage_mono <| (𝒮 i).closedCell_subset_of_mem hi₀
  · rw [not_nonempty_iff] at hι₀
    simp only [iUnion_of_empty, subset_empty_iff] at h𝒮
    cases h𝒮; constructor; simp

namespace CWComplex.Subcomplex

export RelCWComplex.Subcomplex (closedCell_subset_of_mem openCell_subset_of_mem
  cellFrontier_subset_of_mem subset_complex finiteType_subcomplex_of_finiteType
  finiteDimensional_subcomplex_of_finiteDimensional finite_subcomplex_of_finite
  disjoint_openCell_subcomplex_of_not_mem cell_mem_of_mem)

end CWComplex.Subcomplex

section skeleton

/-! In this section we collect results about the `n`-skeleta of CW complexes that depend on their
being complexes in their own right. -/

namespace RelCWComplex
open ContinuousMap
variable [T2Space X] [𝓔 : RelCWComplex C D] {Z} [TopologicalSpace Z]
variable (C)

/-- A CW complex is coherent with its skeleta. -/
lemma isCoherentWith_skeletonLT : IsCoherentWith { C ↓∩ skeletonLT C n | n : ℕ } :=
  Subcomplex.isCoherentWith_cover _ iUnion_skeletonLT_eq_complex.symm.subset

/-- A relative CW complex is coherent with its base and skeleta. -/
lemma isCoherentWith_skeleton :
    IsCoherentWith (insert (C ↓∩ D) { C ↓∩ skeleton C n | n : ℕ }) := by
  fapply 𝓔.isCoherentWith_skeletonLT.enlarge
  rintro _ ⟨_ | n, rfl⟩
  · simpa using .inl (preimage_mono skeletonLT_zero_eq_base.subset)
  · simpa using .inr ⟨n, le_refl _⟩

/-- Descend from a relative CW complex, by providing continuous maps for each skeleton (and the
base) that agree where they intersect. -/
def descBySkeletonLT (f : (n : ℕ) → C(skeletonLT C n, Z))
    (hf : ∀ (n : ℕ) (x : skeletonLT C n),
      f (n + 1) (ContinuousMap.inclusion (skeletonLT_mono <| ENat.coe_le_coe.mpr <| n.le_succ) x)
        = f n x) : C(C, Z) := by?
  fapply isCoherentWith_skeletonLT C |>.liftCover'
  · simp [← preimage_iUnion, iUnion_skeletonLT_eq_complex.symm.subset]
  · exact (f · |>.comp preimageValIncl)
  · intro n m x hx₁ hx₂
    wlog h : m ≤ n generalizing n m
    · exact this m n hx₂ hx₁ (le_of_not_ge h) |>.symm
    induction h with
    | refl => simp
    | @step k hk ih =>
      specialize hf k ⟨x, skeletonLT_mono (ENat.coe_le_coe.mpr hk) hx₂⟩
      simp [ContinuousMap.inclusion] at hf ih ⊢
      simp [hf, ih <| skeletonLT_mono (ENat.coe_le_coe.mpr hk) hx₂]

/-- Composing the descent morphism with the canonical inclusions of each skeleton retrieves the
original maps. -/
lemma descBySkeletonLT_inclusion {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) :
    (descBySkeletonLT C f hf).comp
      (ContinuousMap.inclusion (skeletonLT C n).subset_complex) = f n := by
  ext x
  simp only [SetLike.coe_sort_coe, descBySkeletonLT, ContinuousMap.inclusion, comp_apply, mk_apply,
  Set.inclusion]
  rw [IsCoherentWith.liftCover'_of_mem (i := n)] <;> simp

/-- Composing the descent morphism with the canonical inclusions of each skeleton retrieves the
original map. -/
@[simp]
lemma descBySkeletonLT_inclusion_apply {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf} (n : ℕ) x :
    descBySkeletonLT C f hf
      (Set.inclusion (skeletonLT C n).subset_complex x) = f n x := by
  rw [← descBySkeletonLT_inclusion (hf := hf)]; rfl

lemma descBySkeletonLT_of_mem {f : (n : ℕ) → C(skeletonLT C n, Z)} {hf}
    (n : ℕ) {x} (hx : x ∈ skeletonLT C n) :
    descBySkeletonLT C f hf ⟨x, (skeletonLT C n).subset_complex hx⟩ = f n ⟨x, hx⟩ := by
  rw [← descBySkeletonLT_inclusion (hf := hf)]; rfl

/-- Descend from a relative CW complex, by providing continuous map from each skeleton and
(separately) the base which agree where they intersect. -/
noncomputable def descBySkeleton (d : C(D, Z)) (f : (n : ℕ) → C(skeleton C n, Z))
    (hd : ∀ (x : D), f 0 (ContinuousMap.inclusion (skeleton C 0).base_subset x) = d x)
    (hf : ∀ (n : ℕ) (x : skeleton C n),
      f (n + 1) (ContinuousMap.inclusion (skeleton_mono <| ENat.coe_le_coe.mpr <| n.le_succ) x)
        = f n x) : C(C, Z) :=
  descBySkeletonLT C
    (fun | 0 => d.comp <| .inclusion 𝓔.skeletonLT_zero_eq_base.subset | n + 1 => f n)
    (fun | 0, x => by simp [← hd]; rfl | n + 1, x => by specialize hf n x; simpa using hf)

/-- Composing the descent morphism with the canonical inclusions of each skeleton retrieves the
original map. -/
lemma descBySkeleton_inclusion {d : C(D, Z)} {f : (n : ℕ) → C(skeleton C n, Z)} {hd hf} (n : ℕ) :
    (descBySkeleton C d f hd hf).comp
      (ContinuousMap.inclusion (skeleton C n).subset_complex) = f n := by
  ext x; simpa [descBySkeleton] using descBySkeletonLT_inclusion_apply C (n + 1) x

/-- Composing the descent morphism with the canonical inclusions of each skeleton retrieves the
original map. -/
@[simp]
lemma descBySkeleton_inclusion_apply
    {d : C(D, Z)} {f : (n : ℕ) → C(skeleton C n, Z)} {hd hf} (n : ℕ) x :
    descBySkeleton C d f hd hf
      (Set.inclusion (skeleton C n).subset_complex x) = f n x := by
  rw [← descBySkeleton_inclusion (hd := hd) (hf := hf)]; rfl

/-- Composing the descent morphism with the canonical inclusions from the base retrieves the
original map. -/
lemma descBySkeleton_inclusion_base {d : C(D, Z)} {f : (n : ℕ) → C(skeleton C n, Z)} {hd hf} :
    (descBySkeleton C d f hd hf).comp (ContinuousMap.inclusion base_subset_complex) = d := by
  ext x
  rw [comp_apply, ContinuousMap.coe_inclusion,
    ← Set.inclusion_comp_inclusion 𝓔.skeletonLT_zero_eq_base.symm.subset
    (skeletonLT C 0).subset_complex, Function.comp_apply, descBySkeleton,
    descBySkeletonLT_inclusion_apply]
  rfl

lemma descBySkeleton_of_mem {d : C(D, Z)} {f : (n : ℕ) → C(skeleton C n, Z)} {hd hf}
    (n : ℕ) {x} (hx : x ∈ skeleton C n) :
    descBySkeleton C d f hd hf ⟨x, (skeleton C n).subset_complex hx⟩ = f n ⟨x, hx⟩ := by
  unfold descBySkeleton; rw [descBySkeletonLT_of_mem C (n + 1) hx]; rfl

lemma descBySkeleton_of_mem_base
    {d : C(D, Z)} {f : (n : ℕ) → C(skeleton C n, Z)} {hd hf} {x} (hx : x ∈ D) :
    descBySkeleton C d f hd hf ⟨x, base_subset_complex hx⟩ = d ⟨x, hx⟩ := by
  unfold descBySkeleton; rw [descBySkeletonLT_of_mem C 0 _]
  · rfl
  · rwa [← 𝓔.skeletonLT_zero_eq_base] at hx

end RelCWComplex

namespace CWComplex
variable [T2Space X] [𝓔 : CWComplex C] {Z} [TopologicalSpace Z]
variable (C)

/-- A CW complex is coherent with its skeleta. -/
lemma isCoherentWith_skeleton : IsCoherentWith { C ↓∩ skeleton C n | n : ℕ } := by
  fapply RelCWComplex.isCoherentWith_skeletonLT C |>.enlarge
  rintro _ ⟨_ | n, rfl⟩
  · exists _, ⟨1, rfl⟩; simp [𝓔.skeletonLT_zero_eq_empty]
  · simpa using ⟨n, le_refl _⟩

/-- Descend from a CW complex by providing continuous maps from each skeleton. -/
noncomputable def descBySkeleton
    (f : (n : ℕ) → C(skeleton C n, Z))
    (hf : ∀ (n : ℕ) (x : skeleton C n),
      f (n + 1) (ContinuousMap.inclusion (skeleton_mono <| ENat.coe_le_coe.mpr <| n.le_succ) x)
        = f n x) : C(C, Z) :=
  RelCWComplex.descBySkeletonLT C
    (fun | 0 => .empty Z | n + 1 => f n)
    (fun | 0, x => IsEmpty.elim inferInstance x | n + 1, x => by specialize hf n x; simpa using hf)

/-- Composing the descent morphism with the canonical inclusions of each skeleton retrieves the
original map. -/
lemma descBySkeleton_inclusion {f : (n : ℕ) → C(skeleton C n, Z)} {hf} (n : ℕ) :
    (descBySkeleton C f hf).comp (.inclusion (skeleton C n).subset_complex) = f n := by
  ext x; simpa [descBySkeleton] using RelCWComplex.descBySkeletonLT_inclusion_apply C (n + 1) x

/-- Composing the descent morphism with the canonical inclusions of each skeleton retrieves the
original map. -/
@[simp]
lemma descBySkeleton_inclusion_apply {f : (n : ℕ) → C(skeleton C n, Z)} {hf} (n : ℕ) x :
    descBySkeleton C f hf (Set.inclusion (skeleton C n).subset_complex x) = f n x := by
  simp [descBySkeleton]; rfl

lemma descBySkeleton_of_mem
    {f : (n : ℕ) → C(skeleton C n, Z)} {hf} (n : ℕ) {x} (hx : x ∈ skeleton C n) :
    descBySkeleton C f hf ⟨x, (skeleton C n).subset_complex hx⟩ = f n ⟨x, hx⟩ := by
  unfold descBySkeleton; rw [RelCWComplex.descBySkeletonLT_of_mem C (n + 1) hx]; rfl

end CWComplex
end skeleton

end Topology

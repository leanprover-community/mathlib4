/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.Bases

/-!
# Ultrametric (nonarchimedean) uniform spaces

Ultrametric (nonarchimedean) uniform spaces are ones that generalize ultrametric spaces by
having a uniformity based on equivalence relations.

## Main definitions

In this file we define `IsUltraUniformity`, a Prop mixin typeclass.

## Main results

* `TopologicalSpace.isTopologicalBasis_clopens`: a uniform space with a nonarchimedean uniformity
  has a topological basis of clopen sets in the topology, meaning that it is topologically
  zero-dimensional.

## Implementation notes

As in the `Mathlib/Topology/UniformSpace/Defs.lean` file, we do not reuse `Mathlib/Data/SetRel.lean`
but rather extend the relation properties as needed.

## TODOs

* Prove that `IsUltraUniformity` iff metrizable by `IsUltrametricDist` on a `PseudoMetricSpace`
  under a countable system/basis condition
* Generalize `IsUltrametricDist` to `IsUltrametricUniformity`
* Provide `IsUltraUniformity` for the uniformity in a `Valued` ring
* Generalize results about open/closed balls and spheres in `IsUltraUniformity` to
  combine applications for `MetricSpace.ball` and valued "balls"
* Use `IsUltraUniformity` to work with profinite/totally separated spaces
* Show that the `UniformSpace.Completion` of an `IsUltraUniformity` is `IsUltraUniformity`

## References

* [D. Windisch, *Equivalent characterizations of non-Archimedean uniform spaces*][windisch2021]
* [A. C. M. van Rooij, *Non-Archimedean uniformities*][vanrooij1970]

-/

open Set Filter Topology
open scoped SetRel Uniformity

variable {X : Type*}

/-- The relation is transitive. -/
@[deprecated SetRel.IsTrans (since := "2025-07-10")]
def IsTransitiveRel (V : SetRel X X) : Prop :=
  ∀ ⦃x y z⦄, (x, y) ∈ V → (y, z) ∈ V → (x, z) ∈ V

set_option linter.deprecated false in
@[deprecated SetRel.comp_subset_self (since := "2025-07-10")]
lemma IsTransitiveRel.comp_subset_self {s : SetRel X X}
    (h : IsTransitiveRel s) :
    s ○ s ⊆ s :=
  fun ⟨_, _⟩ ⟨_, hxz, hzy⟩ ↦ h hxz hzy

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_iff_comp_subset_self (since := "2025-07-10")]
lemma isTransitiveRel_iff_comp_subset_self {s : SetRel X X} :
    IsTransitiveRel s ↔ s ○ s ⊆ s :=
  ⟨IsTransitiveRel.comp_subset_self, fun h _ _ _ hx hy ↦ h ⟨_, hx, hy⟩⟩

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_empty (since := "2025-07-10")]
lemma isTransitiveRel_empty : IsTransitiveRel (X := X) ∅ := by
  simp [IsTransitiveRel]

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_univ (since := "2025-07-10")]
lemma isTransitiveRel_univ : IsTransitiveRel (X := X) Set.univ := by
  simp [IsTransitiveRel]

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_singleton (since := "2025-07-10")]
lemma isTransitiveRel_singleton (x y : X) : IsTransitiveRel {(x, y)} := by
  simp +contextual [IsTransitiveRel]

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_inter (since := "2025-07-10")]
lemma IsTransitiveRel.inter {s t : SetRel X X} (hs : IsTransitiveRel s) (ht : IsTransitiveRel t) :
    IsTransitiveRel (s ∩ t) :=
  fun _ _ _ h h' ↦ ⟨hs h.left h'.left, ht h.right h'.right⟩

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_iInter (since := "2025-07-10")]
lemma IsTransitiveRel.iInter {ι : Type*} {U : (i : ι) → SetRel X X}
    (hU : ∀ i, IsTransitiveRel (U i)) :
    IsTransitiveRel (⋂ i, U i) := by
  intro _ _ _ h h'
  simp only [mem_iInter] at h h' ⊢
  intro i
  exact hU i (h i) (h' i)

set_option linter.deprecated false in
@[deprecated SetRel.IsTrans.sInter (since := "2025-07-10")]
lemma IsTransitiveRel.sInter {s : Set (SetRel X X)} (h : ∀ i ∈ s, IsTransitiveRel i) :
    IsTransitiveRel (⋂₀ s) := by
  rw [sInter_eq_iInter]
  exact IsTransitiveRel.iInter (by simpa)

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_preimage (since := "2025-07-10")]
lemma IsTransitiveRel.preimage_prodMap {Y : Type*} {t : Set (Y × Y)}
    (ht : IsTransitiveRel t) (f : X → Y) :
    IsTransitiveRel (Prod.map f f ⁻¹' t) :=
  fun _ _ _ h h' ↦ ht h h'

set_option linter.deprecated false in
@[deprecated SetRel.isTrans_symmetrize (since := "2025-07-10")]
lemma IsTransitiveRel.symmetrizeRel {s : SetRel X X} (h : IsTransitiveRel s) :
    IsTransitiveRel (SetRel.symmetrize s) :=
  fun _ _ _ hxy hyz ↦ ⟨h hxy.1 hyz.1, h hyz.2 hxy.2⟩

set_option linter.deprecated false in
@[deprecated SetRel.comp_eq_self (since := "2025-07-10")]
lemma IsTransitiveRel.comp_eq_of_idRel_subset {s : SetRel X X}
    (h : IsTransitiveRel s) (h' : idRel ⊆ s) :
    s ○ s = s :=
  le_antisymm h.comp_subset_self (subset_comp_self h')

namespace UniformSpace

lemma ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y ∈ ball x V) :
    ball y V ⊆ ball x V :=
  ball_subset_of_comp_subset hy SetRel.comp_subset_self

lemma ball_eq_of_mem {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y ∈ ball x V) :
    ball x V = ball y V := by
  refine le_antisymm (ball_subset_of_mem ?_) (ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry]

end UniformSpace

variable [UniformSpace X]

variable (X) in
/-- A uniform space is ultrametric if the uniformity `𝓤 X` has a basis of equivalence relations. -/
class IsUltraUniformity : Prop where
  hasBasis : (𝓤 X).HasBasis
    (fun s : SetRel X X => s ∈ 𝓤 X ∧ SetRel.IsSymm s ∧ SetRel.IsTrans s) id

lemma IsUltraUniformity.mk_of_hasBasis {ι : Type*} {p : ι → Prop} {s : ι → SetRel X X}
    (h_basis : (𝓤 X).HasBasis p s) (h_symm : ∀ i, p i → SetRel.IsSymm (s i))
    (h_trans : ∀ i, p i → SetRel.IsTrans (s i)) :
    IsUltraUniformity X where
  hasBasis := h_basis.to_hasBasis'
    (fun i hi ↦ ⟨s i, ⟨h_basis.mem_of_mem hi, h_symm i hi, h_trans i hi⟩, subset_rfl⟩)
    (fun _ hs ↦ hs.1)

namespace UniformSpace

lemma isOpen_ball_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsTrans] (h' : V ∈ 𝓤 X) :
    IsOpen (ball x V) := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  exact ⟨V, h', ball_subset_of_mem hy⟩

lemma isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSymm]
    [V.IsTrans] (h' : V ∈ 𝓤 X) :
    IsClosed (ball x V) := by
  rw [← isOpen_compl_iff, isOpen_iff_ball_subset]
  exact fun y hy ↦ ⟨V, h', fun z hyz hxz ↦ hy <| V.trans hxz <| V.symm hyz⟩

@[deprecated (since := "2025-07-10")]
alias isClosed_ball_of_isSymmetricRel_of_isTransitiveRel_of_mem_uniformity :=
  isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity

lemma isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSymm]
    [V.IsTrans] (h' : V ∈ 𝓤 X) :
    IsClopen (ball x V) :=
  ⟨isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity _ ‹_›, isOpen_ball_of_mem_uniformity _ ‹_›⟩

variable [IsUltraUniformity X]

lemma nhds_basis_clopens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id := by
  refine (nhds_basis_uniformity' (IsUltraUniformity.hasBasis)).to_hasBasis' ?_ ?_
  · intro V ⟨hV, h_symm, h_trans⟩
    exact ⟨ball x V, ⟨mem_ball_self _ hV,
      isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity _ hV⟩, le_rfl⟩
  · rintro u ⟨hx, hu⟩
    simp [hu.right.mem_nhds_iff, hx]

/-- A uniform space with a nonarchimedean uniformity is zero-dimensional. -/
lemma _root_.TopologicalSpace.isTopologicalBasis_clopens :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  .of_hasBasis_nhds fun x ↦ by simpa [and_comm] using nhds_basis_clopens x

end UniformSpace

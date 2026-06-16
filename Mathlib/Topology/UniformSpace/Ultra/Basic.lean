/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.Bases

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

As in the `Mathlib/Topology/UniformSpace/Defs.lean` file, we do not reuse `Mathlib/Data/Rel.lean`
but rather extend the relation properties as needed.

## TODOs

* Prove that `IsUltraUniformity` iff metrizable by `IsUltrametricDist` on a `PseudoMetricSpace`
  under a countable system/basis condition
* Generalize `IsUltrametricDist` to `IsUltrametricUniformity`
* Provide `IsUltraUniformity` for the uniformity in a `Valued` ring
* Generalize results about open/closed balls and spheres in `IsUltraUniformity` to
  combine applications for `MetricSpace.ball` and valued "balls"
* Use `IsUltraUniformity` to work with profinite/totally separated spaces

## References

* [D. Windisch, *Equivalent characterizations of non-Archimedean uniform spaces*][windisch2021]
* [A. C. M. van Rooij, *Non-Archimedean uniformities*][vanrooij1970]

-/

@[expose] public section

open Set Filter Topology
open scoped SetRel Uniformity

variable {X : Type*}

lemma IsTransitiveRel.prod_subset_trans {s : SetRel X X} {t u v : Set X} [s.IsTrans]
    (htu : t ×ˢ u ⊆ s) (huv : u ×ˢ v ⊆ s) (hu : u.Nonempty) :
    t ×ˢ v ⊆ s := by
  rintro ⟨a, b⟩ hab
  simp only [mem_prod] at hab
  obtain ⟨x, hx⟩ := hu
  exact s.trans (@htu ⟨a, x⟩ ⟨hab.left, hx⟩) (@huv ⟨x, b⟩ ⟨hx, hab.right⟩)

lemma IsTransitiveRel.mem_filter_prod_trans {s : SetRel X X} {f g h : Filter X} [g.NeBot]
    [s.IsTrans] (hfg : s ∈ f ×ˢ g) (hgh : s ∈ g ×ˢ h) :
    s ∈ f ×ˢ h :=
  Eventually.trans_prod (p := (fun x y ↦ (x, y) ∈ s)) (q := (fun x y ↦ (x, y) ∈ s))
    (r := (fun x y ↦ (x, y) ∈ s)) hfg hgh fun _ _ _ ↦ s.trans

open UniformSpace

lemma ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y ∈ ball x V) :
    ball y V ⊆ ball x V :=
  ball_subset_of_comp_subset hy SetRel.comp_subset_self

lemma ball_eq_of_mem {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y ∈ ball x V) :
    ball x V = ball y V := by
  refine le_antisymm (ball_subset_of_mem ?_) (ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry]

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

lemma IsUltraUniformity.mem_nhds_iff_symm_trans [IsUltraUniformity X] {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 X, SetRel.IsSymm V ∧ SetRel.IsTrans V ∧ UniformSpace.ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    rw [IsUltraUniformity.hasBasis.mem_iff'] at V_in
    obtain ⟨U, ⟨U_in, U_sym, U_trans⟩, U_sub⟩ := V_in
    refine ⟨U, U_in, U_sym, U_trans, (UniformSpace.ball_mono U_sub _).trans V_sub⟩
  · rintro ⟨V, V_in, _, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

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

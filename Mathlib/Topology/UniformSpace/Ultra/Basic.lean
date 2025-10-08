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

open Set Filter Topology
open scoped Uniformity

variable {X : Type*}

/-- The relation is transitive. -/
def IsTransitiveRel (V : Set (X × X)) : Prop :=
  ∀ ⦃x y z⦄, (x, y) ∈ V → (y, z) ∈ V → (x, z) ∈ V

lemma IsTransitiveRel.comp_subset_self {s : Set (X × X)}
    (h : IsTransitiveRel s) :
    s ○ s ⊆ s :=
  fun ⟨_, _⟩ ⟨_, hxz, hzy⟩ ↦ h hxz hzy

lemma isTransitiveRel_iff_comp_subset_self {s : Set (X × X)} :
    IsTransitiveRel s ↔ s ○ s ⊆ s :=
  ⟨IsTransitiveRel.comp_subset_self, fun h _ _ _ hx hy ↦ h ⟨_, hx, hy⟩⟩

lemma isTransitiveRel_empty : IsTransitiveRel (X := X) ∅ := by
  simp [IsTransitiveRel]

lemma isTransitiveRel_idRel : IsTransitiveRel (idRel : Set (X × X)) := by
  simp [IsTransitiveRel, idRel]

lemma isTransitiveRel_univ : IsTransitiveRel (X := X) Set.univ := by
  simp [IsTransitiveRel]

lemma isTransitiveRel_singleton (x y : X) : IsTransitiveRel {(x, y)} := by
  simp +contextual [IsTransitiveRel]

lemma IsTransitiveRel.inter {s t : Set (X × X)} (hs : IsTransitiveRel s) (ht : IsTransitiveRel t) :
    IsTransitiveRel (s ∩ t) :=
  fun _ _ _ h h' ↦ ⟨hs h.left h'.left, ht h.right h'.right⟩

lemma IsTransitiveRel.iInter {ι : Type*} {U : (i : ι) → Set (X × X)}
    (hU : ∀ i, IsTransitiveRel (U i)) :
    IsTransitiveRel (⋂ i, U i) := by
  intro _ _ _ h h'
  simp only [mem_iInter] at h h' ⊢
  intro i
  exact hU i (h i) (h' i)

lemma IsTransitiveRel.sInter {s : Set (Set (X × X))} (h : ∀ i ∈ s, IsTransitiveRel i) :
    IsTransitiveRel (⋂₀ s) := by
  rw [sInter_eq_iInter]
  exact IsTransitiveRel.iInter (by simpa)

lemma IsTransitiveRel.preimage_prodMap {Y : Type*} {t : Set (Y × Y)}
    (ht : IsTransitiveRel t) (f : X → Y) :
    IsTransitiveRel (Prod.map f f ⁻¹' t) :=
  fun _ _ _ h h' ↦ ht h h'

lemma IsTransitiveRel.symmetrizeRel {s : Set (X × X)}
    (h : IsTransitiveRel s) :
    IsTransitiveRel (symmetrizeRel s) :=
  fun _ _ _ hxy hyz ↦ ⟨h hxy.1 hyz.1, h hyz.2 hxy.2⟩

lemma IsTransitiveRel.comp_eq_of_idRel_subset {s : Set (X × X)}
    (h : IsTransitiveRel s) (h' : idRel ⊆ s) :
    s ○ s = s :=
  le_antisymm h.comp_subset_self (subset_comp_self h')

lemma IsTransitiveRel.prod_subset_trans {s : Set (X × X)} {t u v : Set X} (hs : IsTransitiveRel s)
    (htu : t ×ˢ u ⊆ s) (huv : u ×ˢ v ⊆ s) (hu : u.Nonempty) :
    t ×ˢ v ⊆ s := by
  rintro ⟨a, b⟩ hab
  simp only [mem_prod] at hab
  obtain ⟨x, hx⟩ := hu
  exact hs (@htu ⟨a, x⟩ ⟨hab.left, hx⟩) (@huv ⟨x, b⟩ ⟨hx, hab.right⟩)

lemma IsTransitiveRel.mem_filter_prod_trans {s : Set (X × X)} {f g h : Filter X} [g.NeBot]
    (hs : IsTransitiveRel s) (hfg : s ∈ f ×ˢ g) (hgh : s ∈ g ×ˢ h) :
    s ∈ f ×ˢ h :=
  Eventually.trans_prod (by simpa using hfg) (by simpa using hgh) hs

lemma IsTransitiveRel.mem_filter_prod_comm {s : Set (X × X)} {f g h : Filter X} [g.NeBot]
    (hs : IsTransitiveRel s) (hfg : s ∈ f ×ˢ g) (hgh : s ∈ g ×ˢ h) :
    s ∈ f ×ˢ h := by
  rw [mem_prod_iff] at hfg hgh ⊢
  obtain ⟨t, ht, u, hu, htu⟩ := hfg
  obtain ⟨v, hv, w, hw, hvw⟩ := hgh
  replace htu : t ×ˢ (u ∩ v) ⊆ s := by
    rw [Set.prod_inter]
    refine inter_subset_left.trans htu
  replace hvw : (u ∩ v) ×ˢ w ⊆ s := by
    rw [Set.inter_prod]
    refine inter_subset_right.trans hvw
  refine ⟨_, ht, _, hw, hs.prod_subset_trans htu hvw <| g.nonempty_of_mem ?_⟩
  simp [hu, hv]

open UniformSpace in
lemma IsTransitiveRel.ball_subset_of_mem {V : Set (X × X)} (h : IsTransitiveRel V)
    {x y : X} (hy : y ∈ ball x V) :
    ball y V ⊆ ball x V :=
  ball_subset_of_comp_subset hy (h.comp_subset_self)

lemma UniformSpace.ball_eq_of_mem_of_isSymmetricRel_of_isTransitiveRel {V : Set (X × X)}
    (h_symm : IsSymmetricRel V) (h_trans : IsTransitiveRel V) {x y : X}
    (hy : y ∈ ball x V) :
    ball x V = ball y V := by
  refine le_antisymm (h_trans.ball_subset_of_mem ?_) (h_trans.ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry h_symm]

variable [UniformSpace X]

variable (X) in
/-- A uniform space is ultrametric if the uniformity `𝓤 X` has a basis of equivalence relations. -/
class IsUltraUniformity : Prop where
  hasBasis : (𝓤 X).HasBasis
    (fun s : Set (X × X) => s ∈ 𝓤 X ∧ IsSymmetricRel s ∧ IsTransitiveRel s) id

lemma IsUltraUniformity.mk_of_hasBasis {ι : Type*} {p : ι → Prop} {s : ι → Set (X × X)}
    (h_basis : (𝓤 X).HasBasis p s) (h_symm : ∀ i, p i → IsSymmetricRel (s i))
    (h_trans : ∀ i, p i → IsTransitiveRel (s i)) :
    IsUltraUniformity X where
  hasBasis := h_basis.to_hasBasis'
    (fun i hi ↦ ⟨s i, ⟨h_basis.mem_of_mem hi, h_symm i hi, h_trans i hi⟩, subset_rfl⟩)
    (fun _ hs ↦ hs.1)

lemma IsUltraUniformity.mem_nhds_iff_symm_trans [IsUltraUniformity X] {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ V ∈ 𝓤 X, IsSymmetricRel V ∧ IsTransitiveRel V ∧ UniformSpace.ball x V ⊆ s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    rw [IsUltraUniformity.hasBasis.mem_iff'] at V_in
    obtain ⟨U, ⟨U_in, U_sym, U_trans⟩, U_sub⟩ := V_in
    refine ⟨U, U_in, U_sym, U_trans, (UniformSpace.ball_mono U_sub _).trans V_sub⟩
  · rintro ⟨V, V_in, _, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

namespace UniformSpace

lemma _root_.IsTransitiveRel.isOpen_ball_of_mem_uniformity (x : X) {V : Set (X × X)}
    (h : IsTransitiveRel V) (h' : V ∈ 𝓤 X) :
    IsOpen (ball x V) := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  exact ⟨V, h', h.ball_subset_of_mem hy⟩

lemma isClosed_ball_of_isSymmetricRel_of_isTransitiveRel_of_mem_uniformity
    (x : X) {V : Set (X × X)} (h_symm : IsSymmetricRel V)
    (h_trans : IsTransitiveRel V) (h' : V ∈ 𝓤 X) :
    IsClosed (ball x V) := by
  rw [← isOpen_compl_iff, isOpen_iff_ball_subset]
  exact fun y hy ↦ ⟨V, h', fun z hyz hxz ↦ hy <| h_trans hxz <| h_symm.mk_mem_comm.mp hyz⟩

lemma isClopen_ball_of_isSymmetricRel_of_isTransitiveRel_of_mem_uniformity
    (x : X) {V : Set (X × X)} (h_symm : IsSymmetricRel V)
    (h_trans : IsTransitiveRel V) (h' : V ∈ 𝓤 X) :
    IsClopen (ball x V) :=
  ⟨isClosed_ball_of_isSymmetricRel_of_isTransitiveRel_of_mem_uniformity _ ‹_› ‹_› ‹_›,
   h_trans.isOpen_ball_of_mem_uniformity _ ‹_›⟩

variable [IsUltraUniformity X]

lemma nhds_basis_clopens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id := by
  refine (nhds_basis_uniformity' (IsUltraUniformity.hasBasis)).to_hasBasis' ?_ ?_
  · intro V ⟨hV, h_symm, h_trans⟩
    refine ⟨ball x V, ⟨?_,
      isClopen_ball_of_isSymmetricRel_of_isTransitiveRel_of_mem_uniformity _ h_symm h_trans hV⟩,
      le_rfl⟩
    exact mem_ball_self _ hV
  · rintro u ⟨hx, hu⟩
    simp [hu.right.mem_nhds_iff, hx]

/-- A uniform space with a nonarchimedean uniformity is zero-dimensional. -/
lemma _root_.TopologicalSpace.isTopologicalBasis_clopens :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  .of_hasBasis_nhds fun x ↦ by simpa [and_comm] using nhds_basis_clopens x

end UniformSpace

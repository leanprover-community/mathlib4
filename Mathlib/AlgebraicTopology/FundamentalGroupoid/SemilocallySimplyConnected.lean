/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Path
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Homotopy.TubeNeighborhood
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.UnitInterval

/-!
# Semilocally simply connected spaces

A topological space is semilocally simply connected if every point has a neighborhood
such that loops in that neighborhood are nullhomotopic in the whole space.

The definition adopted here is the classical, based one (Brazas, Definition 2.1 in
https://arxiv.org/abs/1102.0993): at each point `x` only loops based at `x` are required to
die in `X`. On locally path-connected spaces — the setting relevant for covering space
theory — this is equivalent to Brazas' strictly stronger *unbased* variant (Definition 2.2),
in which all loops in the neighborhood are required to die; this upgrade is
`SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood`.

## Main definitions

* `SemilocallySimplyConnectedAt x` - The property at a single point: `x` has a neighborhood with
  trivial fundamental group relative to the ambient space.
* `SemilocallySimplyConnectedOn s` - The property holds at every point of `s`.
* `SemilocallySimplyConnectedSpace X` - The property holds at every point of `X`, as a class.

## Main theorems

* `semilocallySimplyConnectedAt_iff` - Characterization in terms of loops being nullhomotopic.
* `semilocallySimplyConnectedAt_iff_paths` - Characterization: there exists a neighborhood `U`
  such that any two paths in `U` between the same endpoints are homotopic.
* `SemilocallySimplyConnectedAt.of_simplyConnected` - Simply connected spaces are semilocally
  simply connected at every point.
* `SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood` - In a locally
  path-connected space, the based condition upgrades to an open, path-connected neighborhood
  in which all loops, at every basepoint, die in the ambient space (Brazas' unbased variant).
* `Path.Homotopic.Quotient.discreteTopology` - In a semilocally simply connected,
  locally path-connected space, the quotient of paths by homotopy has the discrete topology.
-/

noncomputable section

open CategoryTheory Filter FundamentalGroupoid Set Topology

variable {X : Type*} [TopologicalSpace X]

/-! ### SemilocallySimplyConnectedAt -/

/-- A space is semilocally simply connected at `x` if `x` has a neighborhood `U` such that
the map from `π₁(U, x)` to `π₁(X, x)` induced by the inclusion is trivial. Equivalently
(`semilocallySimplyConnectedAt_iff`), every loop at `x` contained in `U` is nullhomotopic
in `X`. In a locally path-connected space the neighborhood can be upgraded to one in which
all loops, at every basepoint, die in `X`
(`SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood`). -/
@[expose] public def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ hx : x ∈ U,
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩).range = ⊥

/-- Simply connected spaces are semilocally simply connected at every point. -/
public theorem SemilocallySimplyConnectedAt.of_simplyConnected [SimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x :=
  ⟨univ, univ_mem, fun hx ↦ by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient x x) _ _⟩

public theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ (γ : Path x x) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl x) := by
  constructor
  · -- Forward direction: SemilocallySimplyConnectedAt implies small loops at `x` are null
    intro ⟨U, hU_nhd, hU_loops⟩
    obtain ⟨V, hVU, hV_open, hx_in_V⟩ := mem_nhds_iff.mp hU_nhd
    refine ⟨V, hV_open, hx_in_V, ?_⟩
    intro γ hγ_range
    -- Since range γ ⊆ V ⊆ U, γ takes values in U
    have hγ_mem : ∀ t, γ t ∈ U := fun t ↦ hVU (hγ_range ⟨t, rfl⟩)
    -- Restrict γ to a path in the subspace U
    let γ_U : Path (⟨x, γ.source ▸ hγ_mem 0⟩ : U) ⟨x, γ.target ▸ hγ_mem 1⟩ := γ.codRestrict hγ_mem
    -- The basepoint x' : U
    let x' : U := ⟨x, γ.source ▸ hγ_mem 0⟩
    -- The map from π₁(U, x') to π₁(X, x) has trivial range
    have h_range := hU_loops x'.2
    rw [MonoidHom.range_eq_bot_iff] at h_range
    have h_map_eq : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x'
        (FundamentalGroup.fromPath ⟦γ_U⟧) =
      FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ := rfl
    have h_map : FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ =
        FundamentalGroup.fromPath ⟦Path.refl x⟧ := by
      rw [← h_map_eq, h_range]; rfl
    rw [Path.map_codRestrict] at h_map
    exact Quotient.eq.mp h_map
  · -- Backward direction: small loops at `x` null implies SemilocallySimplyConnectedAt
    intro ⟨U, hU_open, hx_in_U, hU_loops_null⟩
    refine ⟨U, hU_open.mem_nhds hx_in_U, ?_⟩; intro hx
    simp only [MonoidHom.range_eq_bot_iff]; ext p
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hrange : range (γ'.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ' t).property
    have hhom := hU_loops_null (γ'.map continuous_subtype_val) hrange
    have h_map_eq : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ ⟨x, hx⟩
        (FundamentalGroup.fromPath ⟦γ'⟧) =
      FundamentalGroup.fromPath ⟦γ'.map continuous_subtype_val⟧ := rfl
    rw [h_map_eq, Quotient.sound hhom]
    rfl

/-- Characterization of semilocally simply connected at a point: any two paths in `U` from `x`
to a common endpoint are homotopic. -/
public theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ γ' : Path x u),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    (Path.Homotopic.paths_from_homotopic_iff_loops_nullhomotopic U x).symm

/-! ### SemilocallySimplyConnectedOn -/

variable {s t : Set X} {x : X}

/-- A space is semilocally simply connected on `s` if it is semilocally simply connected
at every point of `s`. -/
@[expose] public def SemilocallySimplyConnectedOn (s : Set X) : Prop :=
  ∀ x ∈ s, SemilocallySimplyConnectedAt x

public theorem SemilocallySimplyConnectedOn.at (h : SemilocallySimplyConnectedOn s) (hx : x ∈ s) :
    SemilocallySimplyConnectedAt x :=
  h x hx

public theorem SemilocallySimplyConnectedOn.mono (h : SemilocallySimplyConnectedOn t)
    (hst : s ⊆ t) : SemilocallySimplyConnectedOn s :=
  fun x hx ↦ h x (hst hx)

public theorem semilocallySimplyConnectedOn_iff :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ (γ : Path x x) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl x) :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff

public theorem semilocallySimplyConnectedOn_iff_paths :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ γ' : Path x u),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff_paths

/-! ### SemilocallySimplyConnectedSpace -/

/-- A topological space is semilocally simply connected if every point has a neighborhood `U`
such that the map from `π₁(U, base)` to `π₁(X, base)` induced by the inclusion is trivial for all
basepoints in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
public class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  exists_small_neighborhood : ∀ x : X, SemilocallySimplyConnectedAt x

public theorem SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace X] (x : X) : SemilocallySimplyConnectedAt x :=
  SemilocallySimplyConnectedSpace.exists_small_neighborhood x

public theorem SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace X] (s : Set X) : SemilocallySimplyConnectedOn s :=
  fun x _ ↦ .of_semilocallySimplyConnectedSpace x

public theorem semilocallySimplyConnectedOn_univ :
    SemilocallySimplyConnectedOn (univ : Set X) ↔ SemilocallySimplyConnectedSpace X :=
  ⟨fun h ↦ ⟨fun x ↦ h x (mem_univ x)⟩, fun ⟨h⟩ x _ ↦ h x⟩

/-- Simply connected spaces are semilocally simply connected. -/
public instance SemilocallySimplyConnectedSpace.of_simplyConnected [SimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace X where
  exists_small_neighborhood x := .of_simplyConnected x

public theorem semilocallySimplyConnectedSpace_iff :
    SemilocallySimplyConnectedSpace X ↔
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ (γ : Path x x) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl x) :=
  ⟨fun ⟨h⟩ x ↦ semilocallySimplyConnectedAt_iff.mp (h x),
    fun h ↦ ⟨fun x ↦ semilocallySimplyConnectedAt_iff.mpr (h x)⟩⟩

public theorem semilocallySimplyConnectedSpace_iff_paths :
    SemilocallySimplyConnectedSpace X ↔
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ γ' : Path x u),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  ⟨fun ⟨h⟩ x ↦ semilocallySimplyConnectedAt_iff_paths.mp (h x),
    fun h ↦ ⟨fun x ↦ semilocallySimplyConnectedAt_iff_paths.mpr (h x)⟩⟩

/-! ### Helper lemmas for discreteness of path homotopy quotients -/

/-- **Upgrade to the unbased condition.** In a locally path-connected space, a point that is
semilocally simply connected has an open, path-connected neighborhood that is
path-homotopy-trivial: all loops in it, at *every* basepoint, are null-homotopic in the
ambient space. This recovers Brazas' unbased variant of semilocal simple connectedness
(Definition 2.2 in https://arxiv.org/abs/1102.0993) from the classical based definition:
take the path component of `x` in a based neighborhood, and conjugate a loop at any of its
points back to `x` along a path inside the component. -/
public theorem SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood
    [LocPathConnectedSpace X] {x : X} (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by
  obtain ⟨U, hU_open, hxU, hU_loops⟩ := semilocallySimplyConnectedAt_iff.mp h
  refine ⟨pathComponentIn U x, hU_open.pathComponentIn x, mem_pathComponentIn_self hxU,
    isPathConnected_pathComponentIn hxU, ?_⟩
  intro a b p q hp hq
  refine (Path.Homotopic.paths_homotopic_iff_loops_nullhomotopic
    (pathComponentIn U x)).mpr (fun {u} δ hδ ↦ ?_) p q hp hq
  -- Conjugate the loop `δ` at `u` back to `x` along a path `α` in `U`.
  have hu : JoinedIn U x u := hδ ⟨0, δ.source⟩
  obtain ⟨α, hα_mem⟩ := hu
  have hconj : range ((α.trans δ).trans α.symm) ⊆ U := by
    simp only [Path.trans_range, Path.symm_range, Set.union_subset_iff]
    exact ⟨⟨range_subset_iff.mpr hα_mem, hδ.trans pathComponentIn_subset⟩,
      range_subset_iff.mpr hα_mem⟩
  exact Path.Homotopic.of_conj_nullhomotopic (hU_loops _ hconj)

/-- In a semilocally simply connected, locally path-connected space, every point has an open
neighborhood `U` with the `IsPathHomotopyTrivial U` property: any two paths in `U` with the
same endpoints are homotopic (so path homotopy classes are determined by endpoints). -/
public theorem exists_uniquePath_neighborhood [SemilocallySimplyConnectedSpace X]
    [LocPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathHomotopyTrivial U :=
  let ⟨U, hU_open, hxU, _, hU⟩ :=
    (SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace
      x).exists_isPathHomotopyTrivial_neighborhood
  ⟨U, hU_open, hxU, hU⟩

/-- In a semilocally simply connected, locally path-connected space, every point has an open,
path-connected, path-homotopy-trivial neighborhood. -/
public theorem exists_pathConnected_slsc_neighborhood [SemilocallySimplyConnectedSpace X]
    [LocPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U :=
  (SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace
    x).exists_isPathHomotopyTrivial_neighborhood

/-- In a semilocally simply connected, locally path-connected space, every path fits in a
tube of path-homotopy-trivial neighborhoods. -/
public theorem Path.exists_partition_in_slsc_neighborhoods [SemilocallySimplyConnectedSpace X]
    [LocPathConnectedSpace X] {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (part : IntervalPartition n) (T : TubeData X x y n), PathInTube γ part T :=
  γ.exists_pathInTube fun z ↦ exists_pathConnected_slsc_neighborhood z

/--
In an SLSC locally path-connected space, every path p has an open tubular neighborhood
contained in its homotopy class.

This shows that the SLSC property gives us not just any open set around p, but specifically
an open set where ALL paths are homotopic to p. This is what makes homotopy classes open.
-/
public theorem Path.exists_open_tubular_neighborhood_in_homotopy_class
    [SemilocallySimplyConnectedSpace X] [LocPathConnectedSpace X]
    {x y : X} (p : Path x y) :
    ∃ (T : Set (Path x y)), IsOpen T ∧ p ∈ T ∧ T ⊆ {p' | Path.Homotopic p' p} := by
  obtain ⟨n, part, T_data, hp_in_tube⟩ := Path.exists_partition_in_slsc_neighborhoods p
  exact ⟨T_data.toSet part, T_data.isOpen part, hp_in_tube,
    fun p' hp' ↦ Path.tube_subset_homotopy_class p part T_data hp_in_tube p' hp'⟩

/-- In an SLSC locally path-connected space, for any path `p`, the set of paths homotopic to `p`
is open. -/
public theorem Path.isOpen_setOf_homotopic [SemilocallySimplyConnectedSpace X]
    [LocPathConnectedSpace X] {x y : X} (p : Path x y) :
    IsOpen {p' : Path x y | Path.Homotopic p' p} := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨T, hT_open, hqT, hT_subset⟩ :=
    exists_open_tubular_neighborhood_in_homotopy_class q
  rw [mem_nhds_iff]
  refine ⟨T, fun p' hp' ↦ (hT_subset hp').trans hq, hT_open, hqT⟩

/-- In a semilocally simply connected, locally path-connected space, the quotient of paths by
homotopy has the discrete topology. -/
public instance Path.Homotopic.Quotient.discreteTopology
    [SemilocallySimplyConnectedSpace X] [LocPathConnectedSpace X] {x y : X} :
    DiscreteTopology (Path.Homotopic.Quotient x y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    apply (Path.Homotopic.Quotient.isQuotientMap_mk x y).isOpen_preimage.mp
    convert isOpen_setOf_homotopic p using 1
    exact Set.ext fun _ ↦ Path.Homotopic.Quotient.eq

end

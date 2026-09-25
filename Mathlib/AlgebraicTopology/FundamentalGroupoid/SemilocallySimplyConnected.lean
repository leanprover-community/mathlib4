/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.TubeNeighborhood

/-!
# Semilocally simply connected spaces

A topological space is semilocally simply connected if every point has a neighborhood such that
loops in that neighborhood are nullhomotopic in the whole space.

We use the classical based definition (Brazas, Definition 2.1 in https://arxiv.org/abs/1102.0993):
at each point `x` only loops based at `x` are required to be nullhomotopic. On locally
path-connected spaces this is equivalent to the unbased variant (Brazas, Definition 2.2), in which
all loops in the neighborhood are required to be nullhomotopic; see
`SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood`.

## Main definitions

* `SemilocallySimplyConnectedAt x`: `x` has a neighborhood `U` such that `π₁(U, x) → π₁(X, x)` is
  trivial.
* `SemilocallySimplyConnectedOn s`: the property holds at every point of `s`.
* `SemilocallySimplyConnectedSpace X`: the property holds at every point of `X`.

## Main statements

* `semilocallySimplyConnectedAt_iff`: characterization in terms of loops being nullhomotopic.
* `semilocallySimplyConnectedAt_iff_paths`: characterization in terms of paths with common
  endpoints being homotopic.
* `SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood`: in a locally
  path-connected space, the neighborhood can be taken open, path-connected and
  path-homotopy-trivial.
* `Path.isOpen_setOf_homotopic` and `Path.Homotopic.Quotient.discreteTopology`: in a semilocally
  simply connected, locally path-connected space, path-homotopy classes are open in the
  compact-open topology, so the quotient of paths by homotopy is discrete.
-/

noncomputable section

open CategoryTheory Filter FundamentalGroupoid Set Topology

variable {X : Type*} [TopologicalSpace X]

/-! ### SemilocallySimplyConnectedAt -/

/-- A space is semilocally simply connected at `x` if `x` has a neighborhood `U` such that the map
`π₁(U, x) → π₁(X, x)` induced by the inclusion is trivial. Equivalently
(`semilocallySimplyConnectedAt_iff`), every loop at `x` in `U` is nullhomotopic in `X`. -/
@[expose] public def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ hx : x ∈ U,
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) ⟨x, hx⟩).range = ⊥

public theorem SemilocallySimplyConnectedAt.of_simplyConnected [SimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x :=
  ⟨univ, univ_mem, fun _ ↦ by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient x x) _ _⟩

public theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  constructor
  · rintro ⟨U, hU, hU_loops⟩
    obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU
    refine ⟨V, hV_open, hxV, fun γ hγ ↦ ?_⟩
    have hγU : ∀ t, γ t ∈ U := fun t ↦ hVU (hγ ⟨t, rfl⟩)
    -- Restrict `γ` to a loop `γ_U` in the subspace `U`; its image in `π₁(X, x)` is trivial.
    let γ_U : Path (⟨x, γ.source ▸ hγU 0⟩ : U) ⟨x, γ.target ▸ hγU 1⟩ := γ.codRestrict hγU
    have h := DFunLike.congr_fun (MonoidHom.range_eq_bot_iff.mp (hU_loops _))
      (FundamentalGroup.fromPath ⟦γ_U⟧)
    rw [FundamentalGroup.map_fromPath, Path.map_codRestrict] at h
    exact Quotient.eq.mp h
  · rintro ⟨U, hU_open, hxU, hU_loops⟩
    refine ⟨U, hU_open.mem_nhds hxU, fun hx ↦ ?_⟩
    simp only [MonoidHom.range_eq_bot_iff]
    ext p
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hγ' : range (γ'.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ' t).property
    rw [FundamentalGroup.map_fromPath, Quotient.sound (hU_loops _ hγ')]
    rfl

/-- A space is semilocally simply connected at `x` iff `x` has an open neighborhood `U` such that
any two paths in `U` from `x` to a common endpoint are homotopic. -/
public theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ {u : X} (γ γ' : Path x u), range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    (Path.Homotopic.paths_from_homotopic_iff_loops_nullhomotopic U x).symm

/-- In a locally path-connected space, a point that is semilocally simply connected has an open,
path-connected neighborhood in which all loops, at every basepoint, are nullhomotopic in the
ambient space. This is Brazas' unbased variant of the definition. -/
public theorem SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood
    [LocallyPathConnectedSpace X] {x : X} (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by
  obtain ⟨U, hU_open, hxU, hU_loops⟩ := semilocallySimplyConnectedAt_iff.mp h
  refine ⟨pathComponentIn U x, hU_open.pathComponentIn x, mem_pathComponentIn_self hxU,
    isPathConnected_pathComponentIn hxU, ?_⟩
  intro a b p q hp hq
  refine (Path.Homotopic.paths_homotopic_iff_loops_nullhomotopic (pathComponentIn U x)).mpr
    (fun {u} δ hδ ↦ ?_) p q hp hq
  -- Conjugate the loop `δ` at `u` back to `x` along a path `α` in the path component.
  obtain ⟨α, hα⟩ : JoinedIn U x u := hδ ⟨0, δ.source⟩
  refine Path.Homotopic.of_conj_nullhomotopic (hU_loops ((α.trans δ).trans α.symm) ?_)
  simp only [Path.trans_range, Path.symm_range, union_subset_iff]
  exact ⟨⟨range_subset_iff.mpr hα, hδ.trans pathComponentIn_subset⟩, range_subset_iff.mpr hα⟩

/-! ### SemilocallySimplyConnectedOn -/

variable {s t : Set X} {x : X}

/-- A space is semilocally simply connected on `s` if it is semilocally simply connected at every
point of `s`. -/
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
        ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff

public theorem semilocallySimplyConnectedOn_iff_paths :
    SemilocallySimplyConnectedOn s ↔
      ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ {u : X} (γ γ' : Path x u), range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff_paths

/-! ### SemilocallySimplyConnectedSpace -/

/-- A topological space is semilocally simply connected if every point `x` has a neighborhood `U`
such that the map `π₁(U, x) → π₁(X, x)` induced by the inclusion is trivial. -/
public class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  semilocallySimplyConnectedAt : ∀ x : X, SemilocallySimplyConnectedAt x

public theorem SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace X] (x : X) : SemilocallySimplyConnectedAt x :=
  SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt x

public theorem SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace X] (s : Set X) : SemilocallySimplyConnectedOn s :=
  fun x _ ↦ .of_semilocallySimplyConnectedSpace x

public theorem semilocallySimplyConnectedOn_univ :
    SemilocallySimplyConnectedOn (univ : Set X) ↔ SemilocallySimplyConnectedSpace X :=
  ⟨fun h ↦ ⟨fun x ↦ h x (mem_univ x)⟩, fun ⟨h⟩ x _ ↦ h x⟩

public instance SemilocallySimplyConnectedSpace.of_simplyConnected [SimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace X where
  semilocallySimplyConnectedAt x := .of_simplyConnected x

public theorem semilocallySimplyConnectedSpace_iff :
    SemilocallySimplyConnectedSpace X ↔
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) :=
  ⟨fun ⟨h⟩ x ↦ semilocallySimplyConnectedAt_iff.mp (h x),
    fun h ↦ ⟨fun x ↦ semilocallySimplyConnectedAt_iff.mpr (h x)⟩⟩

public theorem semilocallySimplyConnectedSpace_iff_paths :
    SemilocallySimplyConnectedSpace X ↔
      ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ {u : X} (γ γ' : Path x u), range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  ⟨fun ⟨h⟩ x ↦ semilocallySimplyConnectedAt_iff_paths.mp (h x),
    fun h ↦ ⟨fun x ↦ semilocallySimplyConnectedAt_iff_paths.mpr (h x)⟩⟩

/-- In a semilocally simply connected, locally path-connected space, every point has an open,
path-connected, path-homotopy-trivial neighborhood. -/
public theorem SemilocallySimplyConnectedSpace.exists_isPathHomotopyTrivial_neighborhood
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U :=
  SemilocallySimplyConnectedAt.exists_isPathHomotopyTrivial_neighborhood
    (.of_semilocallySimplyConnectedSpace x)

/-! ### Discreteness of path-homotopy quotients -/

/-- In a semilocally simply connected, locally path-connected space, every path lies in a tube. -/
public theorem Path.exists_pathInTube_of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (part : IntervalPartition n) (T : TubeData X n), PathInTube γ part T :=
  γ.exists_pathInTube SemilocallySimplyConnectedSpace.exists_isPathHomotopyTrivial_neighborhood

/-- In a semilocally simply connected, locally path-connected space, the set of paths homotopic
to a given path is open in the compact-open topology. -/
public theorem Path.isOpen_setOf_homotopic [SemilocallySimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {x y : X} (p : Path x y) :
    IsOpen {p' : Path x y | p'.Homotopic p} := by
  refine isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_
  obtain ⟨n, part, T, hq_tube⟩ := q.exists_pathInTube_of_semilocallySimplyConnectedSpace
  exact ⟨{q' | PathInTube q' part T}, fun q' hq' ↦ (hq'.homotopic hq_tube).trans hq,
    T.isOpen_setOf_pathInTube_path part x y, hq_tube⟩

/-- In a semilocally simply connected, locally path-connected space, the quotient of paths by
homotopy is discrete. -/
public instance Path.Homotopic.Quotient.discreteTopology
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] {x y : X} :
    DiscreteTopology (Path.Homotopic.Quotient x y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    apply (Path.Homotopic.Quotient.isQuotientMap_mk x y).isOpen_preimage.mp
    convert isOpen_setOf_homotopic p using 1
    exact Set.ext fun _ ↦ Path.Homotopic.Quotient.eq

end

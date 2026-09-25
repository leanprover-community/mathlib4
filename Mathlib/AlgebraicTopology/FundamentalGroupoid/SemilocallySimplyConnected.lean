/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Semilocally simply connected spaces

A topological space is semilocally simply connected if every point `x` has a neighborhood in
which every loop based at `x` is nullhomotopic in the whole space.

## Main definitions

* `SemilocallySimplyConnectedAt x`: `x` has a neighborhood `U` such that `π₁(U, x) → π₁(X, x)` is
  trivial.
* `SemilocallySimplyConnectedOn s`: the property holds at every point of `s`.
* `SemilocallySimplyConnectedSpace X`: the property holds at every point of `X`.

## Main statements

* `semilocallySimplyConnectedAt_iff`: characterization in terms of loops being nullhomotopic.
* `semilocallySimplyConnectedAt_iff_range_eq_bot`: characterization by the inclusion-induced
  map on fundamental groups.
* `semilocallySimplyConnectedAt_iff_paths`: characterization in terms of paths with common
  endpoints being homotopic.

## References

* Fischer, Repovš, Virk and Zastrow,
  [On semilocally simply connected spaces](https://arxiv.org/abs/1102.0993),
  Definitions 2.1 and 2.2.
-/

noncomputable section

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X]

/-! ### SemilocallySimplyConnectedAt -/

/-- A space is semilocally simply connected at `x` if all loops based at `x` in some
neighborhood of `x` are nullhomotopic in the ambient space. -/
@[expose] public def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x)

public theorem SemilocallySimplyConnectedAt.of_simplyConnected [SimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x :=
  ⟨univ, univ_mem, fun γ _ ↦ SimplyConnectedSpace.paths_homotopic γ _⟩

public theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  constructor
  · rintro ⟨U, hU, hU_loops⟩
    obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU
    exact ⟨V, hV_open, hxV, fun γ hγ ↦ hU_loops γ (hγ.trans hVU)⟩
  · rintro ⟨U, hU_open, hxU, hU_loops⟩
    exact ⟨U, hU_open.mem_nhds hxU, hU_loops⟩

/-- The inclusion of a sufficiently small neighborhood induces the trivial map on fundamental
groups. -/
public theorem semilocallySimplyConnectedAt_iff_range_eq_bot {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U ∈ 𝓝 x, ∀ hx : x ∈ U,
        (FundamentalGroup.map (ContinuousMap.subtypeVal U) ⟨x, hx⟩).range = ⊥ := by
  constructor
  · rintro ⟨U, hU, hU_loops⟩
    refine ⟨U, hU, fun hx ↦ ?_⟩
    rw [MonoidHom.range_eq_bot_iff]
    ext p
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hγ : range (γ.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ t).property
    rw [FundamentalGroup.map_fromPath, Quotient.sound (hU_loops _ hγ)]
    rfl
  · rintro ⟨U, hU, hU_loops⟩
    refine ⟨U, hU, fun γ hγ ↦ ?_⟩
    let γU : Path (⟨x, mem_of_mem_nhds hU⟩ : U) ⟨x, mem_of_mem_nhds hU⟩ :=
      γ.codRestrict (fun t ↦ hγ (mem_range_self t))
    have h := DFunLike.congr_fun (MonoidHom.range_eq_bot_iff.mp (hU_loops _))
      (FundamentalGroup.fromPath ⟦γU⟧)
    rw [ContinuousMap.subtypeVal, FundamentalGroup.map_fromPath, Path.map_codRestrict] at h
    exact Quotient.eq.mp h

/-- A space is semilocally simply connected at `x` iff `x` has an open neighborhood `U` such that
any two paths in `U` from `x` to a common endpoint are homotopic. -/
public theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ {u : X} (γ γ' : Path x u), range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  exact exists_congr fun U ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    (Path.Homotopic.paths_from_homotopic_iff_loops_nullhomotopic U x).symm

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

public instance (priority := 100) SemilocallySimplyConnectedSpace.of_simplyConnected
    [SimplyConnectedSpace X] :
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

end

/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Semilocally simply connected spaces

A topological space is semilocally simply connected if every point has a neighborhood
such that loops in that neighborhood are nullhomotopic in the whole space.

## Main definitions

* `SemilocallySimplyConnectedAt x` - The property at a single point: `x` has a neighborhood with
  trivial fundamental group relative to the ambient space.
* `SemilocallySimplyConnectedOn s` - The property holds at every point of `s`.
* `SemilocallySimplyConnected X` - The property holds at every point of `X`.

## Main theorems

* `semilocallySimplyConnectedAt_iff` - Characterization in terms of loops being nullhomotopic.
* `semilocallySimplyConnectedAt_iff_paths` - Characterization: any two paths in U between the same
  endpoints are homotopic.
* `SemilocallySimplyConnectedAt.of_simplyConnected` - Simply connected spaces are semilocally
  simply connected at every point.

## Implementation notes

Our definition quantifies over all basepoints in the neighborhood U (i.e., the inclusion-induced
map `π₁(U, base) → π₁(X, base)` is trivial for all `base ∈ U`). This is sometimes called
"unbased semilocally simply connected" in the literature, and is stronger than the standard
definition which only requires triviality at the point `x` itself. However, the two definitions
are equivalent for locally path-connected spaces, which are the primary context for covering
space theory. See [arXiv:1102.0993](https://arxiv.org/abs/1102.0993), Definitions 2.1 and 2.2.
-/

public section

noncomputable section

open CategoryTheory Filter FundamentalGroupoid Set Topology

variable {X : Type*} [TopologicalSpace X]

/-! ### SemilocallySimplyConnectedAt -/

/-- A space is semilocally simply connected at `x` if `x` has a neighborhood `U` such that
the map from `π₁(U, base)` to `π₁(X, base)` induced by the inclusion is trivial for all
basepoints in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ (base : U),
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) base).range = ⊥

/-- Simply connected spaces are semilocally simply connected at every point. -/
theorem SemilocallySimplyConnectedAt.of_simplyConnected [SimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x :=
  ⟨univ, univ_mem, fun base => by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient base.val base.val) _ _⟩

theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) := by
  constructor
  · -- Forward direction: SemilocallySimplyConnectedAt implies small loops are null
    intro ⟨U, hU_nhd, hU_loops⟩
    obtain ⟨V, hVU, hV_open, hx_in_V⟩ := mem_nhds_iff.mp hU_nhd
    refine ⟨V, hV_open, hx_in_V, ?_⟩
    intro u γ hγ_range
    -- Since range γ ⊆ V ⊆ U, γ takes values in U
    have hγ_mem : ∀ t, γ t ∈ U := fun t => hVU (hγ_range ⟨t, rfl⟩)
    -- Restrict γ to a path in the subspace U
    let γ_U : Path (⟨u, γ.source ▸ hγ_mem 0⟩ : U) ⟨u, γ.target ▸ hγ_mem 1⟩ := γ.codRestrict hγ_mem
    -- The basepoint u' : U
    let u' : U := ⟨u, γ.source ▸ hγ_mem 0⟩
    -- The map from π₁(U, u') to π₁(X, u) has trivial range
    have h_range := hU_loops u'
    rw [MonoidHom.range_eq_bot_iff] at h_range
    have h_map : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u'
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦Path.refl u⟧ := by
      rw [h_range]; rfl
    rw [show FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u'
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ from rfl,
        Path.map_codRestrict] at h_map
    exact Quotient.eq.mp h_map
  · -- Backward direction: small loops null implies SemilocallySimplyConnectedAt
    intro ⟨U, hU_open, hx_in_U, hU_loops_null⟩
    refine ⟨U, hU_open.mem_nhds hx_in_U, ?_⟩; intro base
    simp only [MonoidHom.range_eq_bot_iff]; ext p
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hrange : range (γ'.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ' t).property
    have hhom := hU_loops_null (γ'.map continuous_subtype_val) hrange
    rw [show FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ base
            (FundamentalGroup.fromPath ⟦γ'⟧) =
           FundamentalGroup.fromPath ⟦γ'.map continuous_subtype_val⟧ from rfl,
        Quotient.sound hhom]
    rfl

/-- Characterization of semilocally simply connected at a point: any two paths in U between
the same endpoints are homotopic. -/
theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  constructor
  · intro ⟨U, hU_open, hx_in_U, hU_loops⟩
    refine ⟨U, hU_open, hx_in_U, ?_⟩
    intro u u' γ γ' hγ hγ'
    -- γ.trans γ'.symm is a loop in U, hence nullhomotopic
    have hloop : range (γ.trans γ'.symm) ⊆ U := by
      intro y hy
      simp only [Path.trans_range, Path.symm_range] at hy
      exact hy.elim (fun h => hγ h) (fun h => hγ' h)
    have hnull := hU_loops (γ.trans γ'.symm) hloop
    exact Path.Homotopic.eq_of_trans_symm hnull
  · intro ⟨U, hU_open, hx_in_U, hU_paths⟩
    refine ⟨U, hU_open, hx_in_U, ?_⟩
    intro u γ hγ
    have hrefl : range (Path.refl u) ⊆ U := by
      simp only [Path.refl_range, singleton_subset_iff]
      exact hγ ⟨0, γ.source⟩
    exact hU_paths γ (Path.refl u) hγ hrefl

/-! ### SemilocallySimplyConnectedOn -/

variable {s t : Set X} {x : X}

/-- A space is semilocally simply connected on `s` if it is semilocally simply connected
at every point of `s`. -/
def SemilocallySimplyConnectedOn (s : Set X) : Prop :=
  ∀ x ∈ s, SemilocallySimplyConnectedAt x

theorem SemilocallySimplyConnectedOn.at (h : SemilocallySimplyConnectedOn s) (hx : x ∈ s) :
    SemilocallySimplyConnectedAt x :=
  h x hx

theorem SemilocallySimplyConnectedOn.mono (h : SemilocallySimplyConnectedOn t) (hst : s ⊆ t) :
    SemilocallySimplyConnectedOn s :=
  fun x hx => h x (hst hx)

theorem semilocallySimplyConnectedOn_iff :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) :=
  forall₂_congr fun _ _ => semilocallySimplyConnectedAt_iff

theorem semilocallySimplyConnectedOn_iff_paths :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall₂_congr fun _ _ => semilocallySimplyConnectedAt_iff_paths

/-! ### SemilocallySimplyConnected -/

/-- A topological space is semilocally simply connected if every point has a neighborhood `U`
such that the map from `π₁(U, base)` to `π₁(X, base)` induced by the inclusion is trivial for all
basepoints in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, SemilocallySimplyConnectedAt x

theorem SemilocallySimplyConnected.at (h : SemilocallySimplyConnected X) (x : X) :
    SemilocallySimplyConnectedAt x :=
  h x

theorem SemilocallySimplyConnected.on (h : SemilocallySimplyConnected X) (s : Set X) :
    SemilocallySimplyConnectedOn s :=
  fun x _ => h x

theorem semilocallySimplyConnectedOn_univ :
    SemilocallySimplyConnectedOn (univ : Set X) ↔ SemilocallySimplyConnected X :=
  ⟨fun h x => h x (mem_univ x), fun h x _ => h x⟩

/-- Simply connected spaces are semilocally simply connected. -/
theorem SemilocallySimplyConnected.of_simplyConnected [SimplyConnectedSpace X] :
    SemilocallySimplyConnected X :=
  fun x => SemilocallySimplyConnectedAt.of_simplyConnected x

theorem semilocallySimplyConnected_iff :
    SemilocallySimplyConnected X ↔
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) :=
  forall_congr' fun _ => semilocallySimplyConnectedAt_iff

theorem semilocallySimplyConnected_iff_paths :
    SemilocallySimplyConnected X ↔
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall_congr' fun _ => semilocallySimplyConnectedAt_iff_paths

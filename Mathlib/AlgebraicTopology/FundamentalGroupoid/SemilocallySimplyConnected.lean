/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Path

/-!
# Semilocally simply connected spaces

A topological space is semilocally simply connected if every point has a neighborhood
such that loops in that neighborhood are nullhomotopic in the whole space.

## Main definitions

* `SemilocallySimplyConnected X` - A space where every point has a neighborhood with
  trivial fundamental group relative to the ambient space.

## Main theorems

* `semilocallySimplyConnected_iff_small_loops_null` - Characterization in terms of loops
  being nullhomotopic.
* `SemilocallySimplyConnected.of_simplyConnected` - Simply connected spaces are semilocally
  simply connected.
-/

noncomputable section

open CategoryTheory FundamentalGroupoid

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



/-- A topological space is semilocally simply connected if every point has a neighborhood `U`
such that the inclusion map from `π₁(U, base)` to `π₁(X, base)` is trivial for all basepoints
in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ (base : U), (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ base).range = ⊥

namespace SemilocallySimplyConnected

variable {X : Type*} [TopologicalSpace X]

/-- Simply connected spaces are semilocally simply connected. -/
theorem of_simplyConnected [SimplyConnectedSpace X] : SemilocallySimplyConnected X := by
  intro x
  use Set.univ
  refine ⟨isOpen_univ, Set.mem_univ x, ?_⟩
  intro base
  rw [MonoidHom.range_eq_bot_iff]
  ext p
  -- Both sides are in FundamentalGroup X base.val, which is a subsingleton
  haveI : Subsingleton (FundamentalGroup X base.val) := by
    change Subsingleton (Path.Homotopic.Quotient base.val base.val)
    infer_instance
  apply Subsingleton.elim

theorem semilocallySimplyConnected_iff_small_loops_null
    [LocPathConnectedSpace X] :
    SemilocallySimplyConnected X ↔
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : U} (γ : Path u.val u.val) (_ : Set.range γ ⊆ U),
        Path.Homotopic γ (Path.refl u.val) := by
  constructor
  · -- Forward direction: SemilocallySimplyConnected implies small loops are null
    intro h x
    obtain ⟨U, hU_open, hx_in_U, hU_loops⟩ := h x
    use U, hU_open, hx_in_U
    intro u γ hγ_range
    -- Restrict γ to a path in the subspace U
    have hγ_mem : ∀ t, γ t ∈ U := fun t => hγ_range ⟨t, rfl⟩
    let γ_U : Path u u := {
      toFun := U.codRestrict γ hγ_mem
      continuous_toFun := γ.continuous.codRestrict hγ_mem
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target
    }
    -- The map from π₁(U, u) to π₁(X, u.val) has trivial range
    have h_range := hU_loops u
    rw [MonoidHom.range_eq_bot_iff] at h_range
    -- So it sends ⟦γ_U⟧ to the identity ⟦refl⟧
    have h_map : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u
          (FundamentalGroup.fromPath ⟦γ_U⟧) =
        FundamentalGroup.fromPath ⟦Path.refl u.val⟧ := by
      rw [h_range]
      rfl
    -- The map sends γ_U to γ.map Subtype.val
    -- Since Subtype.val ∘ γ_U = γ pointwise, we have γ_U.map = γ
    have γ_U_eq : γ_U.map continuous_subtype_val = γ := by
      ext t
      rfl
    -- The key is that FundamentalGroup.map sends ⟦γ_U⟧ to ⟦γ_U.map f.continuous⟧
    -- By definition, FundamentalGroup.map is (FundamentalGroupoid.map f).map
    -- which by map_eq and map_lift gives us ⟦γ_U.map⟧
    have : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ := by
      rfl
    rw [this, γ_U_eq] at h_map
    exact Quotient.eq.mp h_map
  · -- Backward direction: small loops null implies SemilocallySimplyConnected
    intro h x
    obtain ⟨U, hU_open, hx_in_U, hU_loops_null⟩ := h x
    use U, hU_open, hx_in_U
    intro base
    rw [MonoidHom.range_eq_bot_iff]
    ext p
    -- p is a loop in the subspace U at base
    -- Extract a representative path from the homotopy class
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    -- The map sends γ' to γ'.map Subtype.val
    -- The range of γ'.map Subtype.val is in U
    have hrange : Set.range (γ'.map continuous_subtype_val) ⊆ U := by
      intro y hy
      obtain ⟨t, rfl⟩ := hy
      simp [Path.map]
      exact (γ' t).property
    -- Apply the hypothesis to get that γ'.map is homotopic to refl
    have hhom : Path.Homotopic (γ'.map continuous_subtype_val) (Path.refl base.val) :=
      hU_loops_null (γ'.map continuous_subtype_val) hrange
    -- FundamentalGroup.map sends ⟦γ'⟧ to ⟦γ'.map⟧
    have h_map_eq : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ base
            (FundamentalGroup.fromPath ⟦γ'⟧) =
           FundamentalGroup.fromPath ⟦γ'.map continuous_subtype_val⟧ := by
      rfl
    -- Since γ'.map is homotopic to refl, the quotients are equal
    have h_quot : (⟦γ'.map continuous_subtype_val⟧ : Path.Homotopic.Quotient base.val base.val) =
           ⟦Path.refl base.val⟧ :=
      Quotient.sound hhom
    rw [h_map_eq, h_quot]
    rfl

end SemilocallySimplyConnected

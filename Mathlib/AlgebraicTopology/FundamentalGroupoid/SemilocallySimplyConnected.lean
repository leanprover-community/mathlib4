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

* `SemilocallySimplyConnected X` - A space where every point has a neighborhood with
  trivial fundamental group relative to the ambient space.

## Main theorems

* `semilocallySimplyConnected_iff` - Characterization in terms of loops
  being nullhomotopic.
* `SemilocallySimplyConnected.of_simplyConnected` - Simply connected spaces are semilocally
  simply connected.
-/

public section

noncomputable section

open CategoryTheory FundamentalGroupoid

variable {X : Type*} [TopologicalSpace X]

/-- A topological space is semilocally simply connected if every point has a neighborhood `U`
such that the map from `π₁(U, base)` to `π₁(X, base)` induced by the inclusion is trivial for all basepoints
in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ (base : U),
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) base).range = ⊥

namespace SemilocallySimplyConnected

variable {X : Type*} [TopologicalSpace X]

/-- Simply connected spaces are semilocally simply connected. -/
theorem of_simplyConnected [SimplyConnectedSpace X] : SemilocallySimplyConnected X := fun x =>
  ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun base => by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient base.val base.val) _ _⟩

theorem semilocallySimplyConnected_iff :
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
    let γ_U := γ.codRestrict hγ_mem
    -- The map from π₁(U, u) to π₁(X, u.val) has trivial range
    have h_range := hU_loops u
    rw [MonoidHom.range_eq_bot_iff] at h_range
    have h_map : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦Path.refl u.val⟧ := by
      rw [h_range]; rfl
    rw [show FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ from rfl,
        Path.map_codRestrict] at h_map
    exact Quotient.eq.mp h_map
  · -- Backward direction: small loops null implies SemilocallySimplyConnected
    intro h x
    obtain ⟨U, hU_open, hx_in_U, hU_loops_null⟩ := h x
    use U, hU_open, hx_in_U; intro base
    simp only [MonoidHom.range_eq_bot_iff]; ext p
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hrange : Set.range (γ'.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ' t).property
    have hhom := hU_loops_null (γ'.map continuous_subtype_val) hrange
    rw [show FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ base
            (FundamentalGroup.fromPath ⟦γ'⟧) =
           FundamentalGroup.fromPath ⟦γ'.map continuous_subtype_val⟧ from rfl,
        Quotient.sound hhom]
    rfl

end SemilocallySimplyConnected

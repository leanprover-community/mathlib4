/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.UniformRing

/-!
# The completion of a nonarchimedean group

The completion of a nonarchimedean group is a nonarchimedean group.

The completion of a nonarchimedean additive group is a nonarchimedean additive group.

The completion of a nonarchimedean ring is a nonarchimedean ring.
-/

open UniformSpace UniformSpace.Completion Subgroup OpenSubgroup Topology

/-- The completion of a nonarchimedean group is a nonarchimedean group. -/
@[to_additive "The completion of a nonarchimedean additive group is a
nonarchimedean additive group."]
instance instNonarchimedeanGroupCompletion {G : Type*} [Group G] [UniformSpace G] [UniformGroup G]
    [NonarchimedeanGroup G] : NonarchimedeanGroup (Completion G) where
  is_nonarchimedean := by
    /- Let `U` be a neighborhood of `1` in `Completion G`. We wish to show that `U` contains an open
    additive subgroup of `Completion G`. -/
    intro U hU
    /- Since `Completion G` is regular, there is a closed neighborhood `C` of `1` which is
    contained in `U`. -/
    obtain ⟨C, ⟨hC, C_closed⟩, C_subset_U⟩ := (closed_nhds_basis 1).mem_iff.mp hU
    /- By continuity, the preimage of `C` in `G`, written `toCompl ⁻¹' U'`,
    is a neighborhood of `0`. -/
    have : toComplMulHom ⁻¹' C ∈ 𝓝 1 :=
      continuous_toComplMulHom.continuousAt.preimage_mem_nhds (by rwa [map_one])
    /- Therefore, since `G` is nonarchimedean, there exists an open subgroup `W` of `G` that is
    contained within `toCompl ⁻¹' C`. -/
    obtain ⟨W, hCW⟩ := NonarchimedeanGroup.is_nonarchimedean (toComplMulHom ⁻¹' C) this
    /- Now, let `V = (W.map toCompl).topologicalClosure` be the result of mapping `W` back to
    `Completion G` and taking the topological closure. -/
    let V : Set (Completion G) := (W.map toComplMulHom).topologicalClosure
    /- We claim that this set `V` satisfies the
    desired properties. There are three conditions to check:

    1. `V` is a subgroup of `Completion G`.
    2. `V` is open.
    3. `V ⊆ U`.

    The first condition follows directly from the fact that the topological closure of a subgroup
    is a subgroup. Now, let us check that `V` is open. -/
    have : IsOpen V := by
      /- Since `V` is a subgroup of `Completion G`, it suffices to show that it is a neighborhood of
      `1` in `Completion G`. This follows from the fact that `toCompl : G → Completion G` is dense
      inducing and `W` is a neighborhood of `1` in `G`. -/
      haveI : ContinuousMul (Completion G) := instContinuousMul
      apply isOpen_of_mem_nhds (g := 1)
      simp only [topologicalClosure_coe, coe_map]
      apply (denseInducing_toComplMulHom _).closure_image_mem_nhds
      rw [coe_toSubgroup]
      exact mem_nhds_one W
    use ⟨_, this⟩
    /- Finally, it remains to show that `V ⊆ U`. It suffices to show that `V ⊆ C`, which
    follows from the fact that `W ⊆ toCompl ⁻¹' C` and `C` is closed. -/
    suffices V ⊆ C from this.trans C_subset_U
    exact closure_minimal (Set.image_subset_iff.mpr hCW) C_closed

/-- The completion of a nonarchimedean ring is a nonarchimedean ring. -/
instance {R : Type*} [Ring R] [UniformSpace R] [TopologicalRing R] [UniformAddGroup R]
    [NonarchimedeanRing R] :
    NonarchimedeanRing (Completion R) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

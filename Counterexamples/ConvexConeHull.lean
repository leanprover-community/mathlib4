/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Analysis.Real.Hyperreal
public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# An open set whose convex cone hull is not open

A topological additive group structure on a module over a linearly ordered field does not suffice
to make the convex cone hull of every open set open.

On the hyperreals, give the additive quotient by the finite elements the discrete topology, and
pull this topology back along the quotient map. Addition and negation are continuous. The coset
of the positive infinite hyperreal `Hyperreal.omega` is open and consists of positive elements.
Its convex cone hull is the positive half-line. This half-line is not open: every open set
containing `1` also contains `0`, because their images in the quotient agree.
-/

@[expose] public noncomputable section

open Set Hyperreal

namespace Counterexample.ConvexConeHull

/-- The additive subgroup of finite hyperreals. -/
def finiteElements : AddSubgroup Hyperreal :=
  (ArchimedeanClass.addValuation Hyperreal).toValuation.valuationSubring.toAddSubgroup

local instance : TopologicalSpace (Hyperreal ⧸ finiteElements) := ⊥

local instance : DiscreteTopology (Hyperreal ⧸ finiteElements) :=
  discreteTopology_bot _

/-- The topology whose open sets are unions of cosets of the finite hyperreals. -/
@[instance_reducible]
def finiteCosetTopology : TopologicalSpace Hyperreal :=
  TopologicalSpace.induced (QuotientAddGroup.mk' finiteElements) ⊥

local instance : TopologicalSpace Hyperreal := finiteCosetTopology

theorem isTopologicalAddGroup_finiteCosetTopology : IsTopologicalAddGroup Hyperreal :=
  isTopologicalAddGroup_induced (QuotientAddGroup.mk' finiteElements)

/-- The coset of the positive infinite hyperreal `Hyperreal.omega`. -/
def infiniteCoset : Set Hyperreal :=
  QuotientAddGroup.mk' finiteElements ⁻¹' {QuotientAddGroup.mk' finiteElements omega}

theorem isOpen_infiniteCoset : IsOpen infiniteCoset :=
  isOpen_induced (isOpen_discrete _)

theorem infiniteCoset_subset_pos : infiniteCoset ⊆ Ioi 0 := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := (QuotientAddGroup.mk'_eq_mk' finiteElements).1 hx
  obtain ⟨n, hn⟩ := ArchimedeanClass.exists_nat_ge_of_mk_nonneg (x := z) hz
  have hnω : (n : Hyperreal) < omega := by
    rw [← map_natCast coeRingHom n]
    exact coe_lt_omega (n : ℝ)
  have hzω : z < omega := hn.trans_lt hnω
  change 0 < x
  simpa only [← hxz, lt_add_iff_pos_left] using hzω

theorem hull_infiniteCoset : (ConvexCone.hull Hyperreal infiniteCoset : Set Hyperreal) = Ioi 0 := by
  refine le_antisymm
    (ConvexCone.hull_min (C := ConvexCone.strictlyPositive Hyperreal Hyperreal)
      infiniteCoset_subset_pos) ?_
  intro x hx
  have hω : omega ∈ ConvexCone.hull Hyperreal infiniteCoset :=
    ConvexCone.subset_hull (by rfl)
  simpa [smul_eq_mul] using
    (ConvexCone.hull Hyperreal infiniteCoset).smul_mem (div_pos hx omega_pos) hω

theorem not_isOpen_hull : ¬ IsOpen (ConvexCone.hull Hyperreal infiniteCoset : Set Hyperreal) := by
  intro h
  obtain ⟨t, _, ht⟩ := isOpen_induced_iff.1 h
  have h1 : QuotientAddGroup.mk' finiteElements 1 ∈ t := by
    change 1 ∈ QuotientAddGroup.mk' finiteElements ⁻¹' t
    rw [ht, hull_infiniteCoset]
    exact (zero_lt_one : (0 : Hyperreal) < 1)
  have h1finite : (1 : Hyperreal) ∈ finiteElements := by
    change 0 ≤ ArchimedeanClass.mk (1 : Hyperreal)
    simp
  have hq : QuotientAddGroup.mk' finiteElements 1 =
      QuotientAddGroup.mk' finiteElements 0 :=
    (QuotientAddGroup.mk'_eq_mk' finiteElements).2
      ⟨-1, finiteElements.neg_mem h1finite, by simp⟩
  have h0 : (0 : Hyperreal) ∈ (ConvexCone.hull Hyperreal infiniteCoset : Set Hyperreal) := by
    rw [← ht]
    change QuotientAddGroup.mk' finiteElements (0 : Hyperreal) ∈ t
    exact hq ▸ h1
  rw [hull_infiniteCoset] at h0
  exact lt_irrefl (0 : Hyperreal) h0

/-- The original hypotheses for `ConvexCone.isOpen_hull` admit a counterexample. -/
theorem isOpen_hull_counterexample :
    ∃ t : TopologicalSpace Hyperreal,
      @IsTopologicalAddGroup Hyperreal t _ ∧
      ∃ s : Set Hyperreal, @IsOpen Hyperreal t s ∧
        ¬ @IsOpen Hyperreal t (ConvexCone.hull Hyperreal s : Set Hyperreal) :=
  ⟨finiteCosetTopology, isTopologicalAddGroup_finiteCosetTopology,
    infiniteCoset, isOpen_infiniteCoset, not_isOpen_hull⟩

end Counterexample.ConvexConeHull

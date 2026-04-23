/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Piecewise
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# Indexed product of sets with unique differentiability property

In this file we prove that the indexed product
of a family sets with unique differentiability property
has the same property, see `UniqueDiffOn.pi` and  `UniqueDiffOn.univ_pi`.
-/

public section

open Filter Set
open scoped Topology

section Semiring

variable {𝕜 : Type*} [Semiring 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)] [∀ i, ContinuousConstSMul 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i}

/-- The tangent cone of a product contains the tangent cone of each factor. -/
theorem mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (Pi.single i) (tangentConeAt 𝕜 (s i) (x i)) (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rw [← tangentConeAt_closure (s := .pi _ _)]
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n ↦ Pi.single i (d n))
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]
  · refine hds.mono fun n hn ↦ ?_
    rw [closure_pi_set, mem_univ_pi]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, subset_closure hn]
  · rw [tendsto_pi_nhds]
    intro j
    rcases eq_or_ne j i with rfl | hj <;> simp [*, tendsto_const_nhds]

theorem UniqueDiffWithinAt.univ_pi {s : ∀ i, Set (E i)} {x : ∀ i, E i}
    (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨.of_closure <| (dense_pi univ fun i _ ↦ (h i).1).closure.mono ?_, fun i _ => (h i).2⟩
  simp only [closure_pi_set, ← Submodule.closure_coe_iSup_map_single, Submodule.map_span]
  gcongr
  refine iSup_le fun i ↦ ?_
  gcongr
  exact mapsTo_tangentConeAt_pi (fun j _ ↦ (h j).2) |>.image_subset

/-- The product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.univ_pi {s : ∀ i, Set (E i)} (h : ∀ i, UniqueDiffOn 𝕜 (s i)) :
    UniqueDiffOn 𝕜 (Set.pi univ s) :=
  fun _x hx ↦ .univ_pi fun i ↦ h i _ <| hx i (mem_univ i)

end Semiring

variable {𝕜 : Type*} [DivisionSemiring 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [TopologicalSpace 𝕜] [(𝓝[≠] (0 : 𝕜)).NeBot]
  [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)] [∀ i, ContinuousSMul 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i} {I : Set ι}

theorem UniqueDiffWithinAt.pi (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.pi (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi fun i hi => h i hi (x i) (hx i hi)

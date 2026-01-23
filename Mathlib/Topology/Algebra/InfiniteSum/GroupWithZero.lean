/-
Copyright Jonathan Washburn (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Infinite products in topological groups with zero

This file provides lemmas about infinite products in types where inversion is only continuous away
from `0` (e.g. normed fields).
-/

public section

noncomputable section

open Filter Finset

open scoped BigOperators Topology

variable {ι G₀ : Type*} {L : SummationFilter ι}

section

variable [CommGroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
variable {f : ι → G₀} {a : G₀}

/-- If `f` has product `a` and `a ≠ 0`, then the pointwise inverse has product `a⁻¹`. -/
theorem HasProd.inv₀ (hf : HasProd f a L) (ha : a ≠ 0) : HasProd (fun i ↦ (f i)⁻¹) a⁻¹ L := by
  have hprod : Tendsto (fun s : Finset ι ↦ ∏ i ∈ s, f i) L.filter (𝓝 a) := by
    simpa [HasProd] using hf
  have hinv :
      Tendsto (fun s : Finset ι ↦ (∏ i ∈ s, f i)⁻¹) L.filter (𝓝 a⁻¹) :=
    hprod.inv₀ ha
  have hcongr :
      (fun s : Finset ι ↦ (∏ i ∈ s, f i)⁻¹) =ᶠ[L.filter] fun s : Finset ι ↦ ∏ i ∈ s, (f i)⁻¹ := by
    refine Filter.Eventually.of_forall fun s ↦ ?_
    simp
  simpa [HasProd] using (hinv.congr' hcongr)

end

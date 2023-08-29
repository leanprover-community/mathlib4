/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.Separation

#align_import dynamics.fixed_points.topology from "leanprover-community/mathlib"@"d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46"

/-!
# Topological properties of fixed points

Currently this file contains two lemmas:

- `isFixedPt_of_tendsto_iterate`: if `f^n(x) → y` and `f` is continuous at `y`, then `f y = y`;
- `isClosed_fixedPoints`: the set of fixed points of a continuous map is a closed set.

## TODO

fixed points, iterates
-/


variable {α : Type*} [TopologicalSpace α] [T2Space α] {f : α → α}

open Function Filter

open Topology

/-- If the iterates `f^[n] x` converge to `y` and `f` is continuous at `y`,
then `y` is a fixed point for `f`. -/
theorem isFixedPt_of_tendsto_iterate {x y : α} (hy : Tendsto (fun n => f^[n] x) atTop (𝓝 y))
    (hf : ContinuousAt f y) : IsFixedPt f y := by
  refine' tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).1 _) hy
  -- ⊢ Tendsto (fun n => f^[n + 1] x) atTop (𝓝 (f y))
  simp only [iterate_succ' f]
  -- ⊢ Tendsto (fun n => (f ∘ f^[n]) x) atTop (𝓝 (f y))
  exact hf.tendsto.comp hy
  -- 🎉 no goals
#align is_fixed_pt_of_tendsto_iterate isFixedPt_of_tendsto_iterate

/-- The set of fixed points of a continuous map is a closed set. -/
theorem isClosed_fixedPoints (hf : Continuous f) : IsClosed (fixedPoints f) :=
  isClosed_eq hf continuous_id
#align is_closed_fixed_points isClosed_fixedPoints

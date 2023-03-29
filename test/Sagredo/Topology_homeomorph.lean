import Mathlib.Tactic.GPT.Sagredo.Dialog
import Mathlib.Topology.Homeomorph

open Set Filter Topology

variable [TopologicalSpace α] [TopologicalSpace β]

namespace Homeomorph

theorem symm_map_nhds_eq' (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  sagredo

  -- rw [h.symm.map_nhds_eq, h.symm_apply_apply]

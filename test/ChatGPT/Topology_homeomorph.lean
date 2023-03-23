import Mathlib.Topology.Homeomorph
import Mathlib.Tactic.ChatGPT.Dialog

open Set Filter Topology

variable [TopologicalSpace α] [TopologicalSpace β]

namespace Homeomorph

theorem symm_map_nhds_eq' (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  gpt

  -- rw [h.symm.map_nhds_eq, h.symm_apply_apply]

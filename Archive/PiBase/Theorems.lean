import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Archive.PiBase.Properties
open Topology Set Filter

universe u
variable (X : Type u) [TopologicalSpace X]

namespace πBase

theorem T119 : P2 X → P1 X := by
  rw [P1, P2]
  intro h
  exact T1Space.t0Space

theorem T226 : P99 X → P2 X := by
  rw [P99, P2]
  intro h
  rw [t1Space_iff_exists_open]
  intro x y
  contrapose; simp at *
  intro hyp
  let f : ℕ → X := fun _ ↦ y
  replace h : Tendsto f atTop (𝓝 x) →
      Tendsto f atTop (𝓝 y) → x = y := by
    apply h
  apply h
  · intro N NNx
    have yinN : y ∈ N := by
      rw [mem_nhds_iff] at NNx
      rcases NNx with ⟨ U, ⟨ UsubN, Uopen, xinU⟩ ⟩
      apply UsubN
      apply hyp
      exact Uopen
      exact xinU
    apply mem_map.mpr
    simp
    use 0
    simp
    intro b
    have : f b = y := by
      simp
    rw [this]
    exact yinN
  · exact tendsto_const_nhds

end πBase

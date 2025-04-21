import Mathlib.Analysis.Normed.Ring.Basic
open Filter
open scoped Topology NNReal

theorem NormedAddCommGroup.tendsto_atBot  {α : Type*} [Nonempty α] [Preorder α]
  [IsDirected α (· ≥  ·)]
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atBot (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≥ n → ‖f n - b‖ < ε :=
  (atBot_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

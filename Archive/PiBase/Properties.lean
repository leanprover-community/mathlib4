import Mathlib.Topology.Basic
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.Basic
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Topology.Category.CompHaus.Basic

open Filter Topology Nontrivial CompHaus

universe u

namespace πBase

abbrev P1 (X : Type u) [TopologicalSpace X] := T0Space X

abbrev P2 (X : Type u) [TopologicalSpace X] := T1Space X

abbrev P78 (X : Type u) [TopologicalSpace X] := Finite X

abbrev P99 (X : Type u) [TopologicalSpace X] :=
  ∀ x y : X, ∀ f : ℕ → X,
    Tendsto f atTop (𝓝 x) → Tendsto f atTop (𝓝 y) →
    x = y

abbrev P125 (X : Type u) [TopologicalSpace X] := Nontrivial X

-- def P171 (X : Type u) [TopologicalSpace X] :=
--   ∀ K, CompHaus K →
--     ∀ f : K → X, ∀ k l : K, f k ≠ f l →
--     ∃ N_k : 𝓝 k, ∃ N_l : 𝓝 l, f'' N_k ∩ f'' N_l = ∅

end πBase

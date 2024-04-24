import Mathlib.Topology.Basic
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.Basic

open Filter Topology

universe u

namespace πBase

def P1 (X : Type u) [TopologicalSpace X] := T0Space X

def P2 (X : Type u) [TopologicalSpace X] := T1Space X

def P99 (X : Type u) [TopologicalSpace X] :=
  ∀ x y : X, ∀ f : ℕ → X,
    Tendsto f atTop (𝓝 x) → Tendsto f atTop (𝓝 y) →
    x = y

end πBase

import Mathlib.Topology.Basic
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.Basic
import Mathlib.Logic.Nontrivial.Basic

open Filter Topology Nontrivial

universe u

namespace πBase

def P1 (X : Type u) [TopologicalSpace X] := T0Space X

def P2 (X : Type u) [TopologicalSpace X] := T1Space X

def P78 (X : Type u) [TopologicalSpace X] := Finite X

def P99 (X : Type u) [TopologicalSpace X] :=
  ∀ x y : X, ∀ f : ℕ → X,
    Tendsto f atTop (𝓝 x) → Tendsto f atTop (𝓝 y) →
    x = y

def P125 (X : Type u) [TopologicalSpace X] := Nontrivial X

end πBase

import Mathlib.Topology.Basic
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.Basic

open Filter Topology

universe u
variable (X : Type u) [TopologicalSpace X]

namespace πBase

def P1 :=
  -- ∀ x y : X, Inseparable x y → x = y
  T0Space X

def P2 :=
  -- ∀ x : X, IsClosed ({x} : Set X)
  T1Space X

def P99 :=
  ∀ x y : X, ∀ f : ℕ → X,
    Tendsto f atTop (𝓝 x) ∧ Tendsto f atTop (𝓝 y) →
    x = y

end πBase

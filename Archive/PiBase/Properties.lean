import Mathlib.Topology.Basic
import Mathlib.Topology.Separation

universe u
variable (X : Type u) [TopologicalSpace X]

namespace πBase

def P1 :=
  -- ∀ x y : X, Inseparable x y → x = y
  T0Space X

def P2 :=
  -- ∀ x : X, IsClosed ({x} : Set X)
  T1Space X

end πBase

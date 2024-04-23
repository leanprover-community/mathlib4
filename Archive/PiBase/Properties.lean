import Mathlib.Topology.Basic
import Mathlib.Topology.Separation

universe u
variable {X : Type u} [TopologicalSpace X]

def πBaseP1 : Prop :=
  -- ∀ x y : X, Inseparable x y → x = y
  T0Space X

def πBaseP2 : Prop :=
  -- ∀ x : X, IsClosed ({x} : Set X)
  T1Space X

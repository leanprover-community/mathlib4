import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Inseparable
open Topology TopologicalSpace

universe u

variable (X : Type u)

def πBaseP1 (_ : TopologicalSpace X) : Prop :=
  ∀ x y : X, Inseparable x y → x = y

def πBaseP2 (_ : TopologicalSpace X) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X)

theorem πBaseT119 (Y : TopologicalSpace X) :
    πBaseP2 X Y → πBaseP1 X Y := by
  intro h
  rw [πBaseP1, πBaseP2] at *
  intro x y g
  rw [Inseparable] at g
  have : IsClosed {y} := by
    apply h y
  sorry

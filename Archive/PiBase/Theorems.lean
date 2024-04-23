import Mathlib.Topology.Basic
import Mathlib.Topology.Inseparable
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Separation
import Archive.PiBase.Properties
open Topology TopologicalSpace Set

universe u
variable (X : Type u) [TopologicalSpace X]

namespace πBase

theorem T119 : P2 X → P1 X := by
  rw [P1, P2]
  intro h
  exact T1Space.t0Space

end πBase

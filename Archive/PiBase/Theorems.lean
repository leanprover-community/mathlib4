import Mathlib.Topology.Basic
import Mathlib.Topology.Inseparable
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Separation
import Archive.PiBase.Properties
open Topology TopologicalSpace Set

universe u
variable {X : Type u} [Xtop : TopologicalSpace X]

theorem πBaseT119 : πBaseP2 X Xtop → πBaseP1 X Xtop := by
  rw [πBaseP1, πBaseP2]
  intro h
  exact T1Space.t0Space

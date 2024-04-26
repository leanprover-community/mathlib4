import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Compactification.OnePoint
open Topology Set Filter Nontrivial Fintype

universe u
variable (X : Type u) [TopologicalSpace X]

namespace πBase

def S20 := OnePoint ℕ

end πBase

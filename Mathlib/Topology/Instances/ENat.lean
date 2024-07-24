import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.Order.Compact

open ENat Filter Topology

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := OrderTopology.mk rfl

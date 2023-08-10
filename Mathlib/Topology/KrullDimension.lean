import Mathlib.Order.KrullDimension
import Mathlib.Topology.SubsetProperties

/--
Krull dimension of a topological space is the supremum of length of chains of closed irreducible
sets.
-/
noncomputable def topologicalKrullDim (T : Type _) [TopologicalSpace T] :
  WithBot (WithTop ℕ) :=
krullDim { s : Set T | IsClosed s ∧ IsIrreducible s }

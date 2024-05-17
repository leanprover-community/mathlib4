/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/

import Mathlib.Topology.Irreducible
import Mathlib.Order.KrullDimension

/-!
# Krull dimension of a topological space

The Krull dimension of a topological space is the order theoretic Krull dimension applied to the
collection of all its subsets that are closed and irreducible. Unfolding this definition, it is
the length of longest series of closed irreducible subsets ordered by inclusion.
-/

/--
The Krull dimension of a topological space is the supremum of length of chains of
closed irreducible sets.
-/
noncomputable def topologicalKrullDim (T : Type _) [TopologicalSpace T] :
  WithBot (WithTop ℕ) :=
krullDim { s : Set T | IsClosed s ∧ IsIrreducible s }

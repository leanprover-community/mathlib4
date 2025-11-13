/-
Copyright (c) 2025 Jasper Mulder-Sohn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent, Jasper Mulder-Sohn
-/
import Mathlib.Data.Set.Pairwise.Lattice
import Mathlib.Order.Preorder.Chain

/-!
# Pairwise results for chains

In this file `Pairwise` results are applied to chains of sets.
-/

open Set

variable {α β : Type*} {c : Set (Set α)} {r : α → α → Prop}
variable (hc : IsChain (· ⊆ ·) c)

namespace IsChain

include hc

lemma pairwise_iUnion₂ : (⋃ s ∈ c, s).Pairwise r ↔ ∀ s ∈ c, s.Pairwise r :=
  pairwise_iUnion₂_iff hc.directedOn

lemma pairwiseDisjoint_iUnion₂ [PartialOrder β] [OrderBot β] (f : α → β) :
    (⋃ s ∈ c, s).PairwiseDisjoint f ↔ ∀ s ∈ c, s.PairwiseDisjoint f :=
  hc.pairwise_iUnion₂

lemma pairwise_sUnion : (⋃₀ c).Pairwise r ↔ ∀ s ∈ c, s.Pairwise r :=
  Set.pairwise_sUnion hc.directedOn

lemma pairwiseDisjoint_sUnion [PartialOrder β] [OrderBot β] (f : α → β) :
    (⋃₀ c).PairwiseDisjoint f ↔ ∀ s ∈ c, s.PairwiseDisjoint f :=
  hc.pairwise_sUnion

end IsChain

/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Tactic.Peel
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.NhdsKer

/-!
# Compactness of the neighborhoods kernel of a set

In this file we prove that the neighborhoods kernel of a set
(defined as the intersection of all of its neighborhoods)
is a compact set if and only if the original set is a compact set.
-/

variable {X : Type*} [TopologicalSpace X] {s : Set X}

theorem IsCompact.nhdsKer_iff : IsCompact (nhdsKer s) ↔ IsCompact s := by
  simp only [isCompact_iff_finite_subcover]
  peel with ι U hUo
  simp only [(isOpen_iUnion hUo).nhdsKer_subset,
    (isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hUo i).nhdsKer_subset]

@[deprecated (since := "2025-07-09")] alias IsCompact.exterior_iff := IsCompact.nhdsKer_iff

protected alias ⟨IsCompact.of_nhdsKer, IsCompact.nhdsKer⟩ := IsCompact.nhdsKer_iff

@[deprecated (since := "2025-07-09")] alias IsCompact.of_exterior := IsCompact.of_nhdsKer
@[deprecated (since := "2025-07-09")] alias IsCompact.exterior := IsCompact.nhdsKer

/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Nonneg.Defs
public import Mathlib.Topology.Constructions

/-!
# Topology on the nonnegative elements of an ordered type

This file endows `Nonneg M` with the topology induced from `M`.
-/

@[expose] public section

open Topology

variable {M : Type*} [Zero M] [LE M] [TopologicalSpace M]

namespace Nonneg

instance instTopologicalSpace : TopologicalSpace (Nonneg M) := .induced val ‹_›

@[fun_prop]
lemma isInducing_val : IsInducing (val : Nonneg M → M) := ⟨rfl⟩

@[fun_prop]
lemma isEmbedding_val : IsEmbedding (val : Nonneg M → M) := ⟨isInducing_val, val_injective⟩

@[continuity, fun_prop]
lemma continuous_val : Continuous (val : Nonneg M → M) := isInducing_val.continuous

end Nonneg

@[continuity, fun_prop]
lemma Continuous.nonnegMk {X : Type*} [TopologicalSpace X] {f : X → M} (hf : Continuous f)
    (hf₀ : ∀ x, 0 ≤ f x) : Continuous fun x ↦ (⟨f x, hf₀ x⟩ : Nonneg M) :=
  Nonneg.isInducing_val.continuous_iff.2 hf

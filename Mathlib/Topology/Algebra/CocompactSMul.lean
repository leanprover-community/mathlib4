/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.ConstMulAction
/-!
# Cocompact actions

In this file we define `CocompactSMul M X` to be a mixin `Prop`-value class
stating that the preimage of a compact set under `(c • ·)` is a compact set.

We also provide 2 instances:
- for a continuous action on a compact Hausdorff space,
- and for a continuous group action on a general space.
-/

/-- A mixin typeclass saying that
the preimage of a compact set under `(c +ᵥ ·)` is a compact set. -/
class CocompactVAdd (M X : Type*) [VAdd M X] [TopologicalSpace X] : Prop where
  /-- The preimage of a compact set under `(c +ᵥ ·)` is a compact set. -/
  isCompact_preimage_vadd (c : M) {s : Set X} (hs : IsCompact s) : IsCompact ((c +ᵥ ·) ⁻¹' s)

/-- A mixin typeclass saying that the preimage of a compact set under `(c • ·)` is a compact set. -/
@[to_additive]
class CocompactSMul (M X : Type*) [SMul M X] [TopologicalSpace X] : Prop where
  /-- The preimage of a compact set under `(c • ·)` is a compact set. -/
  isCompact_preimage_smul (c : M) {s : Set X} (hs : IsCompact s) : IsCompact ((c • ·) ⁻¹' s)

alias CocompactSMul.isCompact_preimage_smul ← IsCompact.preimage_smul
attribute [to_additive] IsCompact.preimage_smul

@[to_additive]
instance (priority := 100) {M X : Type*} [SMul M X] [TopologicalSpace X] [ContinuousConstSMul M X]
    [T2Space X] [CompactSpace X] : CocompactSMul M X :=
  ⟨fun c _s hs ↦ hs.preimage_continuous (continuous_const_smul c)⟩

@[to_additive]
instance (priority := 100) {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [ContinuousConstSMul G X] : CocompactSMul G X :=
  ⟨fun c _s hs ↦ by rw [Set.preimage_smul]; exact hs.smul _⟩

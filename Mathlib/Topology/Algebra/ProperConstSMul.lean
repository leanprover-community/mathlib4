/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Maps.Proper.Basic
/-!
# Actions by proper maps

In this file we define `ProperConstSMul M X` to be a mixin `Prop`-value class
stating that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper action (not yet in `Mathlib`)
which requires `(c, x) ↦ (c • x, x)` to be a proper map.

We also provide 4 instances:
- for a continuous action on a compact Hausdorff space,
- and for a continuous group action on a general space;
- for the action on `X × Y`;
- for the action on `∀ i, X i`.
-/

/-- A mixin typeclass saying that the `(c +ᵥ ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper additive action (not yet in `Mathlib`). -/
class ProperConstVAdd (M X : Type*) [VAdd M X] [TopologicalSpace X] : Prop where
  /-- `(c +ᵥ ·)` is a proper map. -/
  isProperMap_vadd (c : M) : IsProperMap ((c +ᵥ ·) : X → X)

/-- A mixin typeclass saying that `(c • ·)` is a proper map for all `c`.

Note that this is **not** the same as a proper multiplicative action (not yet in `Mathlib`). -/
@[to_additive]
class ProperConstSMul (M X : Type*) [SMul M X] [TopologicalSpace X] : Prop where
  /-- `(c • ·)` is a proper map. -/
  isProperMap_smul (c : M) : IsProperMap ((c • ·) : X → X)

/-- `(c • ·)` is a proper map. -/
@[to_additive /-- `(c +ᵥ ·)` is a proper map. -/]
theorem isProperMap_smul {M : Type*} (c : M) (X : Type*) [SMul M X] [TopologicalSpace X]
    [h : ProperConstSMul M X] : IsProperMap ((c • ·) : X → X) := h.1 c

/-- The preimage of a compact set under `(c • ·)` is a compact set. -/
@[to_additive /-- The preimage of a compact set under `(c +ᵥ ·)` is a compact set. -/]
theorem IsCompact.preimage_smul {M X : Type*} [SMul M X] [TopologicalSpace X]
    [ProperConstSMul M X] {s : Set X} (hs : IsCompact s) (c : M) : IsCompact ((c • ·) ⁻¹' s) :=
  (isProperMap_smul c X).isCompact_preimage hs

@[to_additive]
instance (priority := 100) {M X : Type*} [SMul M X] [TopologicalSpace X] [ContinuousConstSMul M X]
    [T2Space X] [CompactSpace X] : ProperConstSMul M X :=
  ⟨fun c ↦ (continuous_const_smul c).isProperMap⟩

@[to_additive]
instance (priority := 100) {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [ContinuousConstSMul G X] : ProperConstSMul G X :=
  ⟨fun c ↦ (Homeomorph.smul c).isProperMap⟩

instance {M X Y : Type*}
    [SMul M X] [TopologicalSpace X] [ProperConstSMul M X]
    [SMul M Y] [TopologicalSpace Y] [ProperConstSMul M Y] :
    ProperConstSMul M (X × Y) :=
  ⟨fun c ↦ (isProperMap_smul c X).prodMap (isProperMap_smul c Y)⟩

instance {M ι : Type*} {X : ι → Type*}
    [∀ i, SMul M (X i)] [∀ i, TopologicalSpace (X i)] [∀ i, ProperConstSMul M (X i)] :
    ProperConstSMul M (∀ i, X i) :=
  ⟨fun c ↦ .pi_map fun i ↦ isProperMap_smul c (X i)⟩

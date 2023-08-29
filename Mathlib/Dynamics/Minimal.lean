/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Algebra.ConstMulAction

#align_import dynamics.minimal from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Minimal action of a group

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definition
and prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/


open Pointwise

/-- An action of an additive monoid `M` on a topological space is called *minimal* if the `M`-orbit
of every point `x : α` is dense. -/
class AddAction.IsMinimal (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
    Prop where
  dense_orbit : ∀ x : α, Dense (AddAction.orbit M x)
#align add_action.is_minimal AddAction.IsMinimal

/-- An action of a monoid `M` on a topological space is called *minimal* if the `M`-orbit of every
point `x : α` is dense. -/
@[to_additive]
class MulAction.IsMinimal (M α : Type*) [Monoid M] [TopologicalSpace α] [MulAction M α] :
    Prop where
  dense_orbit : ∀ x : α, Dense (MulAction.orbit M x)
#align mul_action.is_minimal MulAction.IsMinimal

open MulAction Set

variable (M G : Type*) {α : Type*} [Monoid M] [Group G] [TopologicalSpace α] [MulAction M α]
  [MulAction G α]

@[to_additive]
theorem MulAction.dense_orbit [IsMinimal M α] (x : α) : Dense (orbit M x) :=
  MulAction.IsMinimal.dense_orbit x
#align mul_action.dense_orbit MulAction.dense_orbit
#align add_action.dense_orbit AddAction.dense_orbit

@[to_additive]
theorem denseRange_smul [IsMinimal M α] (x : α) : DenseRange fun c : M ↦ c • x :=
  MulAction.dense_orbit M x
#align dense_range_smul denseRange_smul
#align dense_range_vadd denseRange_vadd

@[to_additive]
instance (priority := 100) MulAction.isMinimal_of_pretransitive [IsPretransitive M α] :
    IsMinimal M α :=
  ⟨fun x ↦ (surjective_smul M x).denseRange⟩
#align mul_action.is_minimal_of_pretransitive MulAction.isMinimal_of_pretransitive
#align add_action.is_minimal_of_pretransitive AddAction.isMinimal_of_pretransitive

@[to_additive]
theorem IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : ∃ c : M, c • x ∈ U :=
  (denseRange_smul M x).exists_mem_open hUo hne
#align is_open.exists_smul_mem IsOpen.exists_smul_mem
#align is_open.exists_vadd_mem IsOpen.exists_vadd_mem

@[to_additive]
theorem IsOpen.iUnion_preimage_smul [IsMinimal M α] {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : ⋃ c : M, (· • ·) c ⁻¹' U = univ :=
  iUnion_eq_univ_iff.2 fun x ↦ hUo.exists_smul_mem M x hne
#align is_open.Union_preimage_smul IsOpen.iUnion_preimage_smul
#align is_open.Union_preimage_vadd IsOpen.iUnion_preimage_vadd

@[to_additive]
theorem IsOpen.iUnion_smul [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) :
    ⋃ g : G, g • U = univ :=
  iUnion_eq_univ_iff.2 fun x ↦
    let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
    ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩
#align is_open.Union_smul IsOpen.iUnion_smul
#align is_open.Union_vadd IsOpen.iUnion_vadd

@[to_additive]
theorem IsCompact.exists_finite_cover_smul [IsMinimal G α] [ContinuousConstSMul G α]
    {K U : Set α} (hK : IsCompact K) (hUo : IsOpen U) (hne : U.Nonempty) :
    ∃ I : Finset G, K ⊆ ⋃ g ∈ I, g • U :=
  (hK.elim_finite_subcover (fun g ↦ g • U) fun _ ↦ hUo.smul _) <| calc
    K ⊆ univ := subset_univ K
    _ = ⋃ g : G, g • U := (hUo.iUnion_smul G hne).symm
#align is_compact.exists_finite_cover_smul IsCompact.exists_finite_cover_smul
#align is_compact.exists_finite_cover_vadd IsCompact.exists_finite_cover_vadd

@[to_additive]
theorem dense_of_nonempty_smul_invariant [IsMinimal M α] {s : Set α} (hne : s.Nonempty)
    (hsmul : ∀ c : M, c • s ⊆ s) : Dense s :=
  let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2 fun c ↦ hsmul c ⟨x, hx, rfl⟩)
#align dense_of_nonempty_smul_invariant dense_of_nonempty_smul_invariant
#align dense_of_nonempty_vadd_invariant dense_of_nonempty_vadd_invariant

@[to_additive]
theorem eq_empty_or_univ_of_smul_invariant_closed [IsMinimal M α] {s : Set α} (hs : IsClosed s)
    (hsmul : ∀ c : M, c • s ⊆ s) : s = ∅ ∨ s = univ :=
  s.eq_empty_or_nonempty.imp_right fun hne ↦
    hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq
#align eq_empty_or_univ_of_smul_invariant_closed eq_empty_or_univ_of_smul_invariant_closed
#align eq_empty_or_univ_of_vadd_invariant_closed eq_empty_or_univ_of_vadd_invariant_closed

@[to_additive]
theorem isMinimal_iff_closed_smul_invariant [ContinuousConstSMul M α] :
    IsMinimal M α ↔ ∀ s : Set α, IsClosed s → (∀ c : M, c • s ⊆ s) → s = ∅ ∨ s = univ := by
  constructor
  -- ⊢ IsMinimal M α → ∀ (s : Set α), IsClosed s → (∀ (c : M), c • s ⊆ s) → s = ∅ ∨ …
  · intro _ _
    -- ⊢ IsClosed s✝ → (∀ (c : M), c • s✝ ⊆ s✝) → s✝ = ∅ ∨ s✝ = univ
    exact eq_empty_or_univ_of_smul_invariant_closed M
    -- 🎉 no goals
  refine' fun H ↦ ⟨fun _ ↦ dense_iff_closure_eq.2 <| (H _ _ _).resolve_left _⟩
  exacts [isClosed_closure, fun _ ↦ smul_closure_orbit_subset _ _,
    (orbit_nonempty _).closure.ne_empty]
#align is_minimal_iff_closed_smul_invariant isMinimal_iff_closed_smul_invariant
#align is_minimal_iff_closed_vadd_invariant isMinimal_iff_closed_vadd_invariant

/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Exact
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Short exact sequences of topological groups

In this file, we define a short exact sequence of topological groups to a closed embedding `φ`
followed by an open quotient map `ψ` satisfying `φ.range = ψ.ker`.

## Main definitions

* `TopologicalGroup.IsSES φ ψ`: A predicate stating that `φ` is a closed embedding, `ψ` is an open
  quotient map, and `φ.range = ψ.ker`.

-/

@[expose] public section

open scoped Pointwise

/-- A predicate stating that `φ` and `ψ` define a short exact sequence of topological groups. -/
structure TopologicalGroup.IsSES {A B C : Type*} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →* B) (ψ : B →* C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  mulExact : Function.MulExact φ ψ

/-- A predicate stating that `φ` and `ψ` define a short exact sequence of topological groups. -/
structure TopologicalAddGroup.IsSES {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] (φ : A →+ B) (ψ : B →+ C) where
  isClosedEmbedding : Topology.IsClosedEmbedding φ
  isOpenQuotientMap : IsOpenQuotientMap ψ
  exact : Function.Exact φ ψ

attribute [to_additive TopologicalAddGroup.IsSES] TopologicalGroup.IsSES

namespace TopologicalGroup.IsSES

/-- Construct a short exact sequence of topological groups from a closed normal subgroup. -/
@[to_additive /-- Construct a short exact sequence of topological groups from a
closed normal subgroup. -/]
theorem ofClosedSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [H.Normal] (hH : IsClosed (H : Set G)) :
    TopologicalGroup.IsSES H.subtype (QuotientGroup.mk' H) where
  isClosedEmbedding := ⟨⟨Topology.IsInducing.subtypeVal, H.subtype_injective⟩, by simpa⟩
  isOpenQuotientMap := MulAction.isOpenQuotientMap_quotientMk
  mulExact := by simp [Function.MulExact]

variable {A B C E : Type*} [Group A] [Group B] [Group C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {φ : A →* B} {ψ : B →* C} (H : TopologicalGroup.IsSES φ ψ)

end TopologicalGroup.IsSES

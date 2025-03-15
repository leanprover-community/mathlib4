/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Extremal graph theory

This file introduces basic definitions for extremal graph theory, including extremal numbers.

## Main definitions

* `SimpleGraph.extremalNumber` is the maximum number of edges in a `A`-free simple graph on the
  vertex type `β`.

  If `A` is contained in all simple graphs on the vertex type `β`, then this is `0`.

* `SimpleGraph.IsExtremal` is the predicate that `G` satisfies `p` and any `H` satisfying `p` has
  at most as many edges as `G`.
-/


open Finset Fintype

namespace SimpleGraph

variable {V α β γ : Type*} {G : SimpleGraph V}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

section ExtremalNumber

open Classical in
/-- The extremal number of a finite type `β` and a simple graph `A` is the the maximum number of
edges in a `A`-free simple graph on the vertex type `β`.

If `A` is contained in all simple graphs on the vertex type `β`, then this is `0`. -/
noncomputable def extremalNumber (β : Type*) [Fintype β] (A : SimpleGraph α) : ℕ :=
  sup { B : SimpleGraph β | A.Free B } (#·.edgeFinset)

variable [Fintype β] [DecidableRel B.Adj]

/-- If `B` is `A`-free, then `B` has at most `extremalNumber β A` edges. -/
theorem le_extremalNumber (h : A.Free B) : #B.edgeFinset ≤ extremalNumber β A := by
  convert @le_sup _ _ _ _ { B' : SimpleGraph β | A.Free B' }
    (#·.edgeFinset) B (mem_filter.mpr ⟨mem_univ B, h⟩)

/-- If `B` has more than `extremalNumber β A` edges, then `B` contains a copy of `A`. -/
theorem extremalNumber_lt (h : extremalNumber β A < #B.edgeFinset) : A ⊑ B := by
  contrapose! h
  exact le_extremalNumber h

/-- `extremalNumber β A` is at most `x` if and only if every `A`-free simple graph `B` has at most
`x` edges. -/
theorem extremalNumber_le_iff (β : Type*) [Fintype β] (A : SimpleGraph α) (x : ℕ) :
    extremalNumber β A ≤ x ↔
      ∀ (B : SimpleGraph β) [DecidableRel B.Adj], A.Free B → #B.edgeFinset ≤ x := by
  simp_rw [extremalNumber, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun h B _ hB ↦ by convert h B hB, fun h B hB ↦ by convert h B hB⟩

/-- `extremalNumber β A` is greater than `x` if and only if there exists a `A`-free simple graph `B`
with more than `x` edges. -/
theorem lt_extremalNumber_iff (β : Type*) [Fintype β] (A : SimpleGraph α) (x : ℕ) :
    x < extremalNumber β A ↔
      ∃ B : SimpleGraph β, ∃ _ : DecidableRel B.Adj, A.Free B ∧ x < #B.edgeFinset := by
  simp_rw [extremalNumber, Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨B, h₁, h₂⟩ ↦ ⟨B, _, h₁, h₂⟩, fun ⟨B, _, h₁, h₂⟩ ↦ ⟨B, h₁, by convert h₂⟩⟩

variable {R : Type*} [LinearOrderedSemiring R] [FloorSemiring R]

@[inherit_doc extremalNumber_le_iff]
theorem extremalNumber_le_iff_of_nonneg
    (β : Type*) [Fintype β] (A : SimpleGraph α) {x : R} (h : 0 ≤ x) :
    extremalNumber β A ≤ x ↔
      ∀ (B : SimpleGraph β) [DecidableRel B.Adj], A.Free B → #B.edgeFinset ≤ x := by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalNumber_le_iff β A ⌊x⌋₊

@[inherit_doc lt_extremalNumber_iff]
theorem lt_extremalNumber_iff_of_nonneg
    (β : Type*) [Fintype β] (A : SimpleGraph α) {x : R} (h : 0 ≤ x) :
    x < extremalNumber β A ↔
      ∃ B : SimpleGraph β, ∃ _ : DecidableRel B.Adj, A.Free B ∧ x < #B.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalNumber_iff β A ⌊x⌋₊

/-- If `C` contains a copy of `A`, then `extremalNumber β A` is at most `extremalNumber β C`. -/
theorem extremalNumber_of_isContained (h : A ⊑ C) :
    extremalNumber β A ≤ extremalNumber β C := by
  rw [extremalNumber_le_iff]
  intro B _ h'
  contrapose! h'
  rw [not_not]
  exact h.trans (extremalNumber_lt h')

/-- If `β₁ ≃ β₂` and `A₁ ≃g A₂`, then `extremalNumber β₁ A₁` equals `extremalNumber β₂ A₂`. -/
theorem extremalNumber_congr
    {α₁ β₁ α₂ β₂ : Type*} [DecidableEq β₁] [Fintype β₁] [DecidableEq β₂] [Fintype β₂]
    {A₁ : SimpleGraph α₁} {A₂ : SimpleGraph α₂} (e : β₁ ≃ β₂) (φ : A₁ ≃g A₂) :
    extremalNumber β₁ A₁ = extremalNumber β₂ A₂ := by
  rw [Nat.eq_iff_le_and_ge]
  and_intros
  on_goal 2 =>
    replace e := e.symm
    replace φ := φ.symm
  all_goals
    rw [extremalNumber_le_iff]
    intro B _ h
    rw [(Iso.map e B).card_edgeFinset_eq]
    apply le_extremalNumber
    contrapose! h
    rw [not_not] at h ⊢
    exact (h.trans' ⟨φ.toCopy⟩).trans ⟨(Iso.map e B).symm.toCopy⟩

end ExtremalNumber

section IsExtremal

/-- `G` is an extremal graph satisfying `p` if `G` has the maximum number of edges of any simple
graph satisfying `p`. -/
def IsExtremal [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V → Prop) :=
  p G ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj], p H → #H.edgeFinset ≤ #G.edgeFinset

open Classical in
/-- If one simple graph satisfies `p`, then there exists an extremal graph satisfying `p`. -/
theorem exists_isExtremal_iff_exists
    [Fintype V] (p : SimpleGraph V → Prop) [DecidablePred p] :
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, G.IsExtremal p) ↔ ∃ G', p G' := by
  refine ⟨fun ⟨G, _, hp⟩ ↦ ⟨G, hp.1⟩, fun ⟨G', hp'⟩ ↦ ?_⟩
  obtain ⟨G, hp, h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G', by simpa using hp'
  use G, inferInstanceAs (DecidableRel G.Adj)
  exact ⟨by simpa using hp, fun H _ hp' ↦ by convert h H <| mem_filter.mpr ⟨mem_univ H, hp'⟩⟩

open Classical in
/-- If `A` has one edge, then exist an `A.Free` extremal graph. -/
theorem exists_isExtremal_free [Fintype β] (h : A ≠ ⊥) :
    ∃ B : SimpleGraph β, ∃ _ : DecidableRel B.Adj, B.IsExtremal A.Free :=
  (exists_isExtremal_iff_exists A.Free).mpr ⟨⊥, free_bot h⟩

/-- `A`-free extremal graphs are `A`-free simple graphs having `extremalNumber β A` many edges. -/
theorem isExtremal_free_iff [Fintype β] [DecidableRel B.Adj] :
    B.IsExtremal A.Free ↔ (A.Free B) ∧ #B.edgeFinset = extremalNumber β A := by
  rw [IsExtremal, and_congr_right_iff, ← extremalNumber_le_iff]
  exact fun h ↦ ⟨eq_of_le_of_le (le_extremalNumber h), ge_of_eq⟩

end IsExtremal

end SimpleGraph

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

* `SimpleGraph.extremalNumber` is the maximum number of edges in a `H`-free simple graph on `n`
  vertices.

  If `H` is contained in all simple graphs on `n` vertices, then this is `0`.

* `SimpleGraph.IsExtremal` is the predicate that `G` satisfies `p` and any `H` satisfying `p` has
  at most as many edges as `G`.
-/


open Finset Fintype

namespace SimpleGraph

section ExtremalNumber

open Classical in
/-- The extremal number of a natural number `n` and a simple graph `H` is the the maximum number of
edges in a `H`-free simple graph on `n` vertices.

If `H` is contained in all simple graphs on `n` vertices, then this is `0`. -/
noncomputable def extremalNumber (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ :=
  sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

variable {n : ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

open Classical in
theorem extremalNumber_of_fintypeCard_eq [Fintype V] (hc : card V = n) :
    extremalNumber n H = sup { G : SimpleGraph V | H.Free G } (#·.edgeFinset) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalNumber, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  let G' := G.map e.toEmbedding
  replace h' : G' ∈ univ.filter (H.Free ·) := by
    rw [mem_filter, ← free_congr Iso.refl (Iso.map e G)]
    simpa using h
  rw [Iso.card_edgeFinset_eq (Iso.map e G)]
  convert @le_sup _ _ _ _ { G | H.Free G } (#·.edgeFinset) G' h'

variable [Fintype V] [Fintype G.edgeSet]

/-- If `G` is `H`-free, then `G` has at most `extremalNumber (card V) H` edges. -/
theorem card_edgeFinset_le_extremalNumber (h : H.Free G) :
    #G.edgeFinset ≤ extremalNumber (card V) H := by
  rw [extremalNumber_of_fintypeCard_eq rfl]
  convert @le_sup _ _ _ _ { G | H.Free G } (#·.edgeFinset) G (by simpa using h)

/-- If `G` has more than `extremalNumber (card V) H` edges, then `G` contains a copy of `H`. -/
theorem IsContained.of_extremalNumber_lt_card_edgeFinset
    (h : extremalNumber (card V) H < #G.edgeFinset) : H ⊑ G := by
  contrapose! h
  exact card_edgeFinset_le_extremalNumber h

/-- `extremalNumber (card V) H` is at most `x` if and only if every `H`-free simple graph `G` has
at most `x` edges. -/
theorem extremalNumber_le_iff (H : SimpleGraph W) (m : ℕ) :
    extremalNumber (card V) H ≤ m ↔
      ∀ (G : SimpleGraph V) [Fintype G.edgeSet], H.Free G → #G.edgeFinset ≤ m := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun h _ _ h' ↦ by convert h _ h', fun h _ h' ↦ by convert h _ h'⟩

/-- `extremalNumber (card V) H` is greater than `x` if and only if there exists a `H`-free simple
graph `G` with more than `x` edges. -/
theorem lt_extremalNumber_iff (H : SimpleGraph W) (m : ℕ) :
    m < extremalNumber (card V) H ↔
      ∃ G : SimpleGraph V, ∃ _ : Fintype G.edgeSet, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, h, h'⟩ ↦ ⟨_, _, h, h'⟩, fun ⟨_, _, h, h'⟩ ↦ ⟨_, h, by convert h'⟩⟩

variable {R : Type*} [LinearOrderedSemiring R] [FloorSemiring R]

@[inherit_doc extremalNumber_le_iff]
theorem extremalNumber_le_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 ≤ m) :
    extremalNumber (card V) H ≤ m ↔
      ∀ (G : SimpleGraph V) [Fintype G.edgeSet], H.Free G → #G.edgeFinset ≤ m := by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalNumber_le_iff H ⌊m⌋₊

@[inherit_doc lt_extremalNumber_iff]
theorem lt_extremalNumber_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 ≤ m) :
    m < extremalNumber (card V) H ↔
      ∃ G : SimpleGraph V, ∃ _ : Fintype G.edgeSet, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalNumber_iff H ⌊m⌋₊

/-- If `H` contains a copy of `H'`, then `extremalNumber n H` is at most `extremalNumber n H`. -/
theorem IsContained.extremalNumber_le {W' : Type*} {H' : SimpleGraph W'} (h : H' ⊑ H) :
    extremalNumber n H' ≤ extremalNumber n H := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro _ _ h'
  contrapose! h'
  rw [not_not]
  exact h.trans (IsContained.of_extremalNumber_lt_card_edgeFinset h')

/-- If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`. -/
@[congr]
theorem extremalNumber_congr {n₁ n₂ : ℕ} {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁}
    {H₂ : SimpleGraph W₂} (h : n₁ = n₂) (e : H₁ ≃g H₂) :
    extremalNumber n₁ H₁ = extremalNumber n₂ H₂ := by
  rw [h, le_antisymm_iff]
  and_intros
  on_goal 2 =>
    replace e := e.symm
  all_goals
    rw [← Fintype.card_fin n₂, extremalNumber_le_iff]
    intro G _ h
    apply card_edgeFinset_le_extremalNumber
    contrapose! h
    rw [not_free] at h ⊢
    exact h.trans' ⟨e.toCopy⟩

/-- If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`. -/
theorem extremalNumber_congr_right {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
  (e : H₁ ≃g H₂) : extremalNumber n H₁ = extremalNumber n H₂ := extremalNumber_congr rfl e

end ExtremalNumber

section IsExtremal

variable {V W : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]

/-- `G` is an extremal graph satisfying `p` if `G` has the maximum number of edges of any simple
graph satisfying `p`. -/
def IsExtremal (G : SimpleGraph V) [Fintype G.edgeSet] (p : SimpleGraph V → Prop) :=
  p G ∧ ∀ (H : SimpleGraph V) [Fintype H.edgeSet], p H → #H.edgeFinset ≤ #G.edgeFinset

lemma IsExtremal.prop {p : SimpleGraph V → Prop} (h : G.IsExtremal p) : p G := h.1

variable [Fintype V]

open Classical in
/-- If one simple graph satisfies `p`, then there exists an extremal graph satisfying `p`. -/
theorem exists_isExtremal_iff_exists (p : SimpleGraph V → Prop) :
    (∃ G : SimpleGraph V, ∃ _ : Fintype G.edgeSet, G.IsExtremal p) ↔ ∃ G, p G := by
  refine ⟨fun ⟨_, _, h⟩ ↦ ⟨_, h.1⟩, fun ⟨G, hp⟩ ↦ ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G, by simpa using hp
  use G', Fintype.ofFinite G'.edgeSet
  exact ⟨by simpa using hp', fun _ _ hp ↦ by convert h _ (by simpa using hp)⟩

variable {H : SimpleGraph W}

open Classical in
/-- If `H` has one edge, then exist an `H.Free` extremal graph. -/
theorem exists_isExtremal_free (h : H ≠ ⊥) :
    ∃ G : SimpleGraph V, ∃ _ : Fintype G.edgeSet, G.IsExtremal H.Free :=
  (exists_isExtremal_iff_exists H.Free).mpr ⟨⊥, free_bot h⟩

/-- `H`-free extremal graphs are `H`-free simple graphs having `extremalNumber (card V) H` many
edges. -/
theorem isExtremal_free_iff :
    G.IsExtremal H.Free ↔ (H.Free G) ∧ #G.edgeFinset = extremalNumber (card V) H := by
  rw [IsExtremal, and_congr_right_iff, ← extremalNumber_le_iff]
  exact fun h ↦ ⟨eq_of_le_of_le (card_edgeFinset_le_extremalNumber h), ge_of_eq⟩

lemma card_edgeFinset_of_isExtremal_free (h : G.IsExtremal H.Free) :
    #G.edgeFinset = extremalNumber (card V) H := (isExtremal_free_iff.mp h).2

end IsExtremal

end SimpleGraph

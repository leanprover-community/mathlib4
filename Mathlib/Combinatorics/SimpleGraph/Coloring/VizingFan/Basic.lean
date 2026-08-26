/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeChain
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace vizing

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

/-! ### Cardinality Bounds on Missing Colors -/

set_option linter.unusedDecidableInType false in
/-- The number of colors missing at `v` is at least `Fintype.card α − G.degree v`. -/
lemma missingColors_ncard_ge
    [Fintype α] [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : G.lineGraph.Coloring α) (v : V) :
    Fintype.card α ≤ G.degree v + (missingColors c v).ncard := by
  have h_compl : (incidentColors c v).ncard + (missingColors c v).ncard = Fintype.card α := by
    unfold missingColors
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h_bound : (incidentColors c v).ncard ≤ G.degree v :=
    incidentColors_ncard_le_degree c v
  omega

set_option linter.unusedDecidableInType false in
/-- If at least `G.degree v + 2` colors are available, then at least two colors
    are missing at `v`. -/
lemma missingColors_ncard_ge_two
    [Fintype α] [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : G.lineGraph.Coloring α) (v : V)
    (h : G.degree v + 2 ≤ Fintype.card α) :
    2 ≤ (missingColors c v).ncard := by
  have := missingColors_ncard_ge c v
  omega

/-! ### Fan Structure -/

/-- A **Vizing fan** `[v₀, v₁, …, vₖ]` with apex `u` rooted at `v = v₀`.

    The defining properties are:
    1. `l.head? = some v` — the list starts at `v`.
    2. `l.Nodup` — the fan vertices are distinct.
    3. For each consecutive pair `(vᵢ, vᵢ₊₁)`, there exists an edge
       `e : G.edgeSet` with `e = s(u, vᵢ₊₁)` whose color under `c` is
       missing at `vᵢ`. -/
def IsFan (c : G.lineGraph.Coloring α) (u v : V) (l : List V) : Prop :=
  l.head? = some v ∧
  l.Nodup ∧
  l.IsChain (fun a b =>
    ∃ e : G.edgeSet, e.val = s(u, b) ∧ c.toFun e ∈ missingColors c a)

/-- The trivial fan `[v]` is always a fan from `u` rooted at `v`. -/
lemma IsFan.singleton (c : G.lineGraph.Coloring α) (u v : V) :
    IsFan c u v [v] :=
  ⟨rfl, List.nodup_singleton v, List.isChain_singleton v⟩

/-- Fan length is at most `Fintype.card V` (from `Nodup`). -/
lemma IsFan.length_le_card
    [Fintype V]
    {c : G.lineGraph.Coloring α} {u v : V} {l : List V} (h : IsFan c u v l) :
    l.length ≤ Fintype.card V := by
  classical
  obtain ⟨_, h_nodup, _⟩ := h
  rw [← List.toFinset_card_of_nodup h_nodup]
  exact Finset.card_le_univ _

/-! ### Maximality Dichotomy -/

/-- `w` extends a fan with last vertex `vk` when the color of the edge
    `s(u, w)` is missing at `vk`. -/
def IsFanExtension (c : G.lineGraph.Coloring α) (u vk w : V) : Prop :=
  ∃ e : G.edgeSet, e.val = s(u, w) ∧ c.toFun e ∈ missingColors c vk

/-- A maximal fan satisfies exactly one of two terminal conditions:
    - **Term-A**: some color is missing at both `u` and the last fan vertex `vₖ`.
    - **Term-B**: every color missing at `vₖ` is already the color of some
      fan edge `s(u, vⱼ)`. -/
lemma IsFan.dichotomy
    {c : G.lineGraph.Coloring α} {u v : V} {l : List V}
    (_h : IsFan c u v l) (h_ne : l ≠ [])
    (h_max : ∀ w : V, w ∉ l → ¬ IsFanExtension c u (l.getLast h_ne) w) :
    (∃ γ : α, γ ∈ missingColors c u ∧ γ ∈ missingColors c (l.getLast h_ne))
    ∨
    (∀ γ : α, γ ∈ missingColors c (l.getLast h_ne) →
       ∃ w ∈ l, ∃ e : G.edgeSet, e.val = s(u, w) ∧ c.toFun e = γ) := by
  set vk := l.getLast h_ne
  by_cases h_ta : ∃ γ : α, γ ∈ missingColors c u ∧ γ ∈ missingColors c vk
  · exact Or.inl h_ta
  · right
    push Not at h_ta
    intro γ hγ_vk
    have hγ_used : γ ∈ incidentColors c u := by
      have hγ_not_missing : γ ∉ missingColors c u := fun h => h_ta γ h hγ_vk
      -- missingColors = incidentColorsᶜ, so ∉ missing → ∈ incident.
      by_contra h_not_inc
      exact hγ_not_missing h_not_inc
    obtain ⟨e, he_inc, he_col⟩ := hγ_used
    obtain ⟨a, b, hab⟩ : ∃ a b : V, e.val = s(a, b) :=
      e.val.ind (fun a b => ⟨a, b, rfl⟩)
    have hu_in : u ∈ e.val := he_inc
    rw [hab, Sym2.mem_iff] at hu_in
    rcases hu_in with rfl | rfl
    · refine ⟨b, ?_, e, hab, he_col⟩
      by_contra h_b_notin
      exact h_max b h_b_notin ⟨e, hab, he_col ▸ hγ_vk⟩
    · refine ⟨a, ?_, e, ?_, he_col⟩
      · by_contra h_a_notin
        exact h_max a h_a_notin ⟨e, by rw [hab, Sym2.eq_swap], he_col ▸ hγ_vk⟩
      · rw [hab, Sym2.eq_swap]


end vizing

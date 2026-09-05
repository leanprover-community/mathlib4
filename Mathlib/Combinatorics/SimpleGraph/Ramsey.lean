/-
Copyright (c) 2026 Haoyu Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoyu Chen
-/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Nat.Choose.Central

/-!
# Ramsey's theorem (finite, two-colour) with the Erdős–Szekeres bound

This file formalises **Ramsey's theorem** for graphs, in the quantitative form proved by
Erdős and Szekeres (1935):

> every graph on at least `(s + t - 2).choose (s - 1)` vertices contains either a clique of
> size `s` or an independent set of size `t`.

## Main results

* `SimpleGraph.exists_isNClique_or_isNIndepSet` — the "shifted index" workhorse: a vertex set of
  size at least `(a + b).choose a` contains an `(a+1)`-clique or a `(b+1)`-independent set.
* `SimpleGraph.ramsey` — Ramsey's theorem in the classical indexing: for `1 ≤ s`, `1 ≤ t`,
  a vertex set of size at least `(s + t - 2).choose (s - 1)` contains an `s`-clique or a
  `t`-independent set.
* `SimpleGraph.ramsey_univ` — the same statement for a finite vertex type.
* `SimpleGraph.ramsey_diagonal` — the diagonal bound `R(s, s) ≤ 4 ^ (s - 1)`.
* `SimpleGraph.ramsey_two_colouring` — the classical edge-two-colouring phrasing.
* `SimpleGraph.ramseyNumber` — the Ramsey number `R(s, t)`, with
  `SimpleGraph.exists_ramseyNumber` (existence), `SimpleGraph.ramseyNumber_le` (the
  Erdős–Szekeres upper bound), `SimpleGraph.ramseyNumber_diagonal_le`
  (`R(s, s) ≤ 4 ^ (s - 1)`) and `SimpleGraph.ramseyNumber_comm` (symmetry).
* `SimpleGraph.ramseyNumber_one_left`, `SimpleGraph.ramseyNumber_two_left` — the exact values
  `R(1, t) = 1` and `R(2, t) = t`.
* `SimpleGraph.ramseyNumber_three_three` — the exact value `R(3, 3) = 6`; the lower bound is
  witnessed by the 5-cycle.
* `SimpleGraph.schur_two_colours` — **Schur's theorem** for two colours with the sharp bound
  `S(2) ≤ 5`, deduced from `R(3, 3) ≤ 6`.

## Proof

The classical Erdős–Szekeres double induction. Given a vertex `v` in a set `V` of at least
`(a + b + 2).choose (a + 1)` vertices, split `V.erase v` into the neighbours `N` and the
non-neighbours `M` of `v`. Pascal's rule
`(a + b + 2).choose (a + 1) = (a + b + 1).choose a + (a + b + 1).choose (a + 1)`
forces `(a + b + 1).choose a ≤ #N` or `(a + b + 1).choose (a + 1) ≤ #M`; in the first case
induction gives an `(a+1)`-clique inside `N` (extend by `v`) or a `(b+2)`-independent set, in
the second case induction gives an `(a+2)`-clique or a `(b+1)`-independent set inside `M`
(extend by `v`).

## References

* P. Erdős and G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935).
* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (1930).
-/

open Finset

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] (G : SimpleGraph α)

omit [DecidableEq α] in
/-- A singleton is a `1`-independent set. -/
theorem isNIndepSet_singleton (a : α) : G.IsNIndepSet 1 {a} := by
  refine ⟨?_, by simp⟩
  simp [SimpleGraph.IsIndepSet]

/-- Adding a vertex nonadjacent to (and distinct from) every element of an independent set
gives a larger independent set. This is the independent-set analogue of
`SimpleGraph.IsNClique.insert`. -/
theorem IsNIndepSet.insert {G : SimpleGraph α} {n : ℕ} {s : Finset α} {a : α}
    (hs : G.IsNIndepSet n s)
    (h : ∀ b ∈ s, a ≠ b ∧ ¬ G.Adj a b) : G.IsNIndepSet (n + 1) (insert a s) := by
  rw [← isNClique_compl] at hs ⊢
  exact hs.insert fun b hb => by simpa [SimpleGraph.compl_adj] using h b hb

/-- **Erdős–Szekeres / Ramsey**, shifted-index form.

If a finite set `V` of vertices of a graph `G` has at least `(a + b).choose a` elements, then
`V` contains a clique of size `a + 1` or an independent set of size `b + 1`. -/
theorem exists_isNClique_or_isNIndepSet :
    ∀ (a b : ℕ) (V : Finset α), (a + b).choose a ≤ #V →
      (∃ A ⊆ V, G.IsNClique (a + 1) A) ∨ (∃ B ⊆ V, G.IsNIndepSet (b + 1) B) := by
  classical
  intro a
  induction a with
  | zero =>
    -- `(0 + b).choose 0 = 1`, so `V` is nonempty and any singleton is a `1`-clique.
    intro b V hV
    simp only [Nat.zero_add, Nat.choose_zero_right] at hV
    obtain ⟨v, hv⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one hV)
    exact Or.inl ⟨{v}, Finset.singleton_subset_iff.2 hv, isNClique_singleton.2 rfl⟩
  | succ a iha =>
    intro b
    induction b with
    | zero =>
      -- `(a + 1 + 0).choose (a + 1) = 1`, so `V` is nonempty and any singleton is a
      -- `1`-independent set.
      intro V hV
      simp only [Nat.add_zero, Nat.choose_self] at hV
      obtain ⟨v, hv⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one hV)
      exact Or.inr ⟨{v}, Finset.singleton_subset_iff.2 hv, G.isNIndepSet_singleton v⟩
    | succ b ihb =>
      intro V hV
      -- Pick a vertex `v ∈ V`.
      have hpos : 0 < ((a + 1) + (b + 1)).choose (a + 1) :=
        Nat.choose_pos (by omega)
      obtain ⟨v, hv⟩ := Finset.card_pos.1 (lt_of_lt_of_le hpos hV)
      set N : Finset α := (V.erase v).filter (fun w => G.Adj v w) with hN
      set M : Finset α := (V.erase v).filter (fun w => ¬ G.Adj v w) with hM
      have hNV : N ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hMV : M ⊆ V := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      -- Counting: `#N + #M = #V - 1`.
      have hcards : #N + #M = #(V.erase v) :=
        Finset.card_filter_add_card_filter_not (fun w => G.Adj v w)
      have herase : #(V.erase v) = #V - 1 := Finset.card_erase_of_mem hv
      -- Pascal's rule.
      have hpascal : ((a + 1) + (b + 1)).choose (a + 1)
          = ((a + b + 1)).choose a + ((a + b + 1)).choose (a + 1) := by
        have : (a + 1) + (b + 1) = (a + b + 1) + 1 := by ring
        rw [this, Nat.choose_succ_succ]
      have hVpos : 1 ≤ #V := hpos.trans_le hV
      -- One of the two sides is large enough.
      have hsplit : (a + b + 1).choose a ≤ #N ∨ (a + b + 1).choose (a + 1) ≤ #M := by
        rcases le_or_gt ((a + b + 1).choose a) #N with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      rcases hsplit with hbig | hbig
      · -- `v` has many neighbours: induct on `a`, with `b + 1` on the other side.
        have := iha (b + 1) N (by simpa [Nat.add_assoc] using hbig)
        rcases this with ⟨A, hAN, hA⟩ | ⟨B, hBN, hB⟩
        · -- Extend the `(a+1)`-clique inside `N` by `v`.
          refine Or.inl ⟨insert v A, ?_, ?_⟩
          · exact Finset.insert_subset hv (hAN.trans hNV)
          · refine hA.insert fun w hw => ?_
            have := hAN hw
            rw [hN, Finset.mem_filter] at this
            exact this.2
        · exact Or.inr ⟨B, hBN.trans hNV, hB⟩
      · -- `v` has many non-neighbours: induct on `b`.
        have := ihb M (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbig)
        rcases this with ⟨A, hAM, hA⟩ | ⟨B, hBM, hB⟩
        · exact Or.inl ⟨A, hAM.trans hMV, hA⟩
        · -- Extend the `(b+1)`-independent set inside `M` by `v`.
          refine Or.inr ⟨insert v B, ?_, ?_⟩
          · exact Finset.insert_subset hv (hBM.trans hMV)
          · refine hB.insert fun w hw => ?_
            have hwM := hBM hw
            rw [hM, Finset.mem_filter, Finset.mem_erase] at hwM
            exact ⟨fun h => hwM.1.1 h.symm, hwM.2⟩

/-- **Ramsey's theorem** with the Erdős–Szekeres bound.

For `s, t ≥ 1`, any finite set `V` of vertices of a graph `G` with
`(s + t - 2).choose (s - 1) ≤ #V` contains a clique of size `s` or an independent set of
size `t`. Equivalently, the Ramsey number satisfies `R(s, t) ≤ (s + t - 2).choose (s - 1)`. -/
theorem ramsey {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (V : Finset α)
    (hV : (s + t - 2).choose (s - 1) ≤ #V) :
    (∃ A ⊆ V, G.IsNClique s A) ∨ (∃ B ⊆ V, G.IsNIndepSet t B) := by
  obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
  refine G.exists_isNClique_or_isNIndepSet a b V ?_
  have h1 : a + 1 + (b + 1) - 2 = a + b := by omega
  have h2 : a + 1 - 1 = a := by omega
  rwa [h1, h2] at hV

/-- **Ramsey's theorem** for a finite vertex type: if `(s + t - 2).choose (s - 1) ≤ card α`
then the graph `G` has a clique of size `s` or an independent set of size `t`. -/
theorem ramsey_univ [Fintype α] {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hcard : (s + t - 2).choose (s - 1) ≤ Fintype.card α) :
    (∃ A : Finset α, G.IsNClique s A) ∨ (∃ B : Finset α, G.IsNIndepSet t B) := by
  have := G.ramsey hs ht Finset.univ (by simpa [Finset.card_univ] using hcard)
  rcases this with ⟨A, _, hA⟩ | ⟨B, _, hB⟩
  · exact Or.inl ⟨A, hA⟩
  · exact Or.inr ⟨B, hB⟩

/-- The diagonal Ramsey bound `R(s, s) ≤ 4 ^ (s - 1)`: any vertex set of size at least
`4 ^ (s - 1)` contains a clique or an independent set of size `s`. -/
theorem ramsey_diagonal {s : ℕ} (hs : 1 ≤ s) (V : Finset α) (hV : 4 ^ (s - 1) ≤ #V) :
    (∃ A ⊆ V, G.IsNClique s A) ∨ (∃ B ⊆ V, G.IsNIndepSet s B) := by
  refine G.ramsey hs hs V (le_trans ?_ hV)
  obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
  rw [show a + 1 + (a + 1) - 2 = 2 * a by omega, show a + 1 - 1 = a by omega]
  simpa [Nat.centralBinom] using Nat.centralBinom_le_four_pow a

/-- **Ramsey's theorem, edge-colouring form.**

Colour every pair of distinct elements of `α` with a colour in `Bool` (via a symmetric
function `c`). If `V` is a finite set of at least `(s + t - 2).choose (s - 1)` elements, then
`V` has a subset of size `s` all of whose pairs are coloured `true`, or a subset of size `t`
all of whose pairs are coloured `false`. -/
theorem ramsey_two_colouring {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (c : α → α → Bool)
    (hsymm : ∀ i j, c i j = c j i) (V : Finset α)
    (hV : (s + t - 2).choose (s - 1) ≤ #V) :
    (∃ A ⊆ V, #A = s ∧ ∀ i ∈ A, ∀ j ∈ A, i ≠ j → c i j = true) ∨
      (∃ B ⊆ V, #B = t ∧ ∀ i ∈ B, ∀ j ∈ B, i ≠ j → c i j = false) := by
  classical
  set H : SimpleGraph α :=
    { Adj := fun i j => i ≠ j ∧ c i j = true
      symm := ⟨fun i j h => ⟨h.1.symm, by rw [hsymm]; exact h.2⟩⟩
      loopless := ⟨fun i h => h.1 rfl⟩ } with hH
  rcases H.ramsey hs ht V hV with ⟨A, hAV, hA⟩ | ⟨B, hBV, hB⟩
  · refine Or.inl ⟨A, hAV, hA.card_eq, fun i hi j hj hne => ?_⟩
    exact (hA.isClique hi hj hne).2
  · refine Or.inr ⟨B, hBV, hB.card_eq, fun i hi j hj hne => ?_⟩
    have := hB.isIndepSet hi hj hne
    simp only [hH] at this
    rcases Bool.eq_false_or_eq_true (c i j) with h | h
    · exact absurd ⟨hne, h⟩ this
    · exact h

/-! ### Ramsey numbers -/

/-- `IsRamseyBound s t n` says that `n` vertices always suffice: in every graph, every set of
at least `n` vertices contains a clique of size `s` or an independent set of size `t`. -/
def IsRamseyBound (s t n : ℕ) : Prop :=
  ∀ (β : Type) [DecidableEq β] (H : SimpleGraph β) (V : Finset β), n ≤ #V →
    (∃ A ⊆ V, H.IsNClique s A) ∨ (∃ B ⊆ V, H.IsNIndepSet t B)

theorem IsRamseyBound.mono {s t n m : ℕ} (h : IsRamseyBound s t n) (hnm : n ≤ m) :
    IsRamseyBound s t m := fun _β _ H V hV => h _β H V (hnm.trans hV)

/-- The **Ramsey number** `R(s, t)`: the least number of vertices that forces a clique of size
`s` or an independent set of size `t`. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := sInf {n | IsRamseyBound s t n}

/-- **Ramsey numbers exist**: for `s, t ≥ 1` some finite `n` forces an `s`-clique or a
`t`-independent set. -/
theorem exists_ramseyNumber {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    {n | IsRamseyBound s t n}.Nonempty :=
  ⟨(s + t - 2).choose (s - 1), fun _β _ H V hV => H.ramsey hs ht V hV⟩

/-- The **Erdős–Szekeres bound** on Ramsey numbers: `R(s, t) ≤ (s + t - 2).choose (s - 1)`. -/
theorem ramseyNumber_le {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ramseyNumber s t ≤ (s + t - 2).choose (s - 1) :=
  Nat.sInf_le (fun _β _ H V hV => H.ramsey hs ht V hV)

/-- `ramseyNumber` really is a Ramsey bound. -/
theorem isRamseyBound_ramseyNumber {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    IsRamseyBound s t (ramseyNumber s t) :=
  Nat.sInf_mem (exists_ramseyNumber hs ht)

/-- The diagonal Ramsey bound `R(s, s) ≤ 4 ^ (s - 1)`. -/
theorem ramseyNumber_diagonal_le {s : ℕ} (hs : 1 ≤ s) : ramseyNumber s s ≤ 4 ^ (s - 1) :=
  Nat.sInf_le (fun _β _ H V hV => H.ramsey_diagonal hs V hV)

/-- `R(3, 3) ≤ 6`: any six vertices contain a triangle or three pairwise nonadjacent
vertices. -/
theorem ramseyNumber_three_three_le : ramseyNumber 3 3 ≤ 6 :=
  calc ramseyNumber 3 3 ≤ (3 + 3 - 2).choose (3 - 1) :=
        ramseyNumber_le (by norm_num) (by norm_num)
    _ = 6 := by decide

/-- Ramsey bounds are symmetric in the two parameters (pass to the complement graph). -/
theorem IsRamseyBound.symm {s t n : ℕ} (h : IsRamseyBound s t n) : IsRamseyBound t s n := by
  intro β _ H V hV
  rcases h β Hᶜ V hV with ⟨A, hAV, hA⟩ | ⟨B, hBV, hB⟩
  · exact Or.inr ⟨A, hAV, (isNClique_compl H).1 hA⟩
  · exact Or.inl ⟨B, hBV, (isNIndepSet_compl H).1 hB⟩

/-- Ramsey numbers are symmetric: `R(s, t) = R(t, s)`. -/
theorem ramseyNumber_comm (s t : ℕ) : ramseyNumber s t = ramseyNumber t s := by
  have hset : {n | IsRamseyBound s t n} = {n | IsRamseyBound t s n} := by
    ext n
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [ramseyNumber, ramseyNumber, hset]

/-! ### Exact small Ramsey numbers -/

/-- `R(1, t) = 1` for `t ≥ 1`. -/
theorem ramseyNumber_one_left {t : ℕ} (ht : 1 ≤ t) : ramseyNumber 1 t = 1 := by
  refine le_antisymm ?_ ?_
  · have := ramseyNumber_le (s := 1) (t := t) le_rfl ht
    simpa using this
  · by_contra hcon
    have h0 : IsRamseyBound 1 t 0 :=
      (isRamseyBound_ramseyNumber le_rfl ht).mono (by omega)
    rcases h0 ℕ ⊥ ∅ (by simp) with ⟨A, hA, hA'⟩ | ⟨B, hB, hB'⟩
    · rw [Finset.subset_empty] at hA
      subst hA
      simpa using hA'.card_eq
    · rw [Finset.subset_empty] at hB
      subst hB
      have := hB'.card_eq
      simp only [Finset.card_empty] at this
      omega

/-- `R(2, t) = t` for `t ≥ 1`: the empty graph on `t - 1` vertices has no edge and no
independent set of size `t`. -/
theorem ramseyNumber_two_left {t : ℕ} (ht : 1 ≤ t) : ramseyNumber 2 t = t := by
  refine le_antisymm ?_ ?_
  · have := ramseyNumber_le (s := 2) (t := t) (by norm_num) ht
    simpa using this
  · by_contra hcon
    have h0 : IsRamseyBound 2 t (t - 1) :=
      (isRamseyBound_ramseyNumber (by norm_num) ht).mono (by omega)
    have hcard : (t - 1) ≤ #(Finset.univ : Finset (Fin (t - 1))) := by simp
    rcases h0 (Fin (t - 1)) ⊥ Finset.univ hcard with ⟨A, _, hA⟩ | ⟨B, _, hB⟩
    · exact (cliqueFree_bot (le_refl 2) A) hA
    · have h1 : #B ≤ t - 1 := by
        simpa using Finset.card_le_card (Finset.subset_univ B)
      have h2 := hB.card_eq
      omega

/-! ### The exact value `R(3, 3) = 6` -/

/-- The 5-cycle `C₅` contains no triangle and no independent set of size `3`, so five vertices
do not suffice: `R(3, 3) > 5`. -/
theorem not_isRamseyBound_three_three_five : ¬ IsRamseyBound 3 3 5 := by
  intro h
  have hc : (5 : ℕ) ≤ #(Finset.univ : Finset (Fin 5)) := by simp
  have := h (Fin 5) (cycleGraph 5) Finset.univ hc
  revert this
  decide

/-- **`R(3, 3) = 6`**: every graph on six vertices contains a triangle or three pairwise
nonadjacent vertices, and the 5-cycle shows that five vertices do not suffice. -/
theorem ramseyNumber_three_three : ramseyNumber 3 3 = 6 := by
  refine le_antisymm ramseyNumber_three_three_le ?_
  by_contra hcon
  exact not_isRamseyBound_three_three_five
    ((isRamseyBound_ramseyNumber (by norm_num) (by norm_num)).mono (by omega))

/-! ### Schur's theorem for two colours -/

/-- From a three-element finite set of naturals we can read off its elements in increasing
order. -/
theorem exists_lt_lt_of_card_eq_three {A : Finset ℕ} (h : #A = 3) :
    ∃ p q r, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ p < q ∧ q < r := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 h
  rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy b c with h2 | h2 | h2 <;>
    rcases lt_trichotomy a c with h3 | h3 | h3 <;>
    first
      | exact ⟨a, b, c, by simp, by simp, by simp, by omega, by omega⟩
      | exact ⟨a, c, b, by simp, by simp, by simp, by omega, by omega⟩
      | exact ⟨b, a, c, by simp, by simp, by simp, by omega, by omega⟩
      | exact ⟨b, c, a, by simp, by simp, by simp, by omega, by omega⟩
      | exact ⟨c, a, b, by simp, by simp, by simp, by omega, by omega⟩
      | exact ⟨c, b, a, by simp, by simp, by simp, by omega, by omega⟩

/-- **Schur's theorem for two colours**, with the sharp bound `S(2) ≤ 5`.

For any two-colouring `c` of `{1, …, 5}` there are `x, y, z ∈ {1, …, 5}` of the same colour
with `x + y = z`. This is deduced from `R(3, 3) ≤ 6` by colouring the pair `i < j` with the
colour of `j - i`. -/
theorem schur_two_colours (c : ℕ → Bool) :
    ∃ x y z : ℕ, x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ z ∈ Finset.Icc 1 5 ∧
      x + y = z ∧ c x = c z ∧ c y = c z := by
  classical
  -- Colour the pair `{i, j}` with the colour of `|i - j|`.
  set d : ℕ → ℕ → Bool := fun i j => c (if i < j then j - i else i - j) with hd
  have hdsymm : ∀ i j, d i j = d j i := by
    intro i j
    simp only [hd]
    congr 1
    split_ifs <;> omega
  have hcard : (3 + 3 - 2).choose (3 - 1) ≤ #(Finset.Icc 1 6) := by
    rw [Nat.card_Icc]
    decide
  -- Extract a monochromatic triangle inside `{1, …, 6}`.
  have key : ∃ (A : Finset ℕ) (v : Bool), A ⊆ Finset.Icc 1 6 ∧ #A = 3 ∧
      ∀ i ∈ A, ∀ j ∈ A, i ≠ j → d i j = v := by
    rcases ramsey_two_colouring (s := 3) (t := 3) (by norm_num) (by norm_num) d hdsymm
        (Finset.Icc 1 6) hcard with ⟨A, hA, hA3, hAc⟩ | ⟨B, hB, hB3, hBc⟩
    · exact ⟨A, true, hA, hA3, hAc⟩
    · exact ⟨B, false, hB, hB3, hBc⟩
  obtain ⟨A, v, hA, hA3, hAc⟩ := key
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr⟩ := exists_lt_lt_of_card_eq_three hA3
  have hp1 : 1 ≤ p ∧ p ≤ 6 := by simpa using hA hp
  have hr1 : 1 ≤ r ∧ r ≤ 6 := by simpa using hA hr
  have e1 : c (q - p) = v := by
    have := hAc p hp q hq (by omega)
    simpa [hd, hpq] using this
  have e2 : c (r - q) = v := by
    have := hAc q hq r hr (by omega)
    simpa [hd, hqr] using this
  have e3 : c (r - p) = v := by
    have := hAc p hp r hr (by omega)
    simpa [hd, hpq.trans hqr] using this
  refine ⟨q - p, r - q, r - p, ?_, ?_, ?_, by omega, by rw [e1, e3], by rw [e2, e3]⟩ <;>
    simp only [Finset.mem_Icc] <;> omega

end SimpleGraph

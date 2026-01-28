/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Yue Sun, Nick Adfor
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Parity

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs.

## Main definitions

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph
* `SimpleGraph.cycleGraph.bicoloring_of_even`: Bicoloring of even cycles
* `SimpleGraph.cycleGraph.tricoloring`: Tricoloring of odd cycles


## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph
* `SimpleGraph.cycleGraph.bicoloring_of_even`: Bicoloring of even cycles
* `SimpleGraph.cycleGraph.tricoloring`: Tricoloring of odd cycles
* `SimpleGraph.bipartite_iff_all_cycles_even`:
  Proves that `G.IsBipartite` iff `G` does not contain an odd cycle.
  I.e., `G.IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G`.

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

/-- The chromatic number of a graph is at most 2 if and only if the graph is bipartite -/
theorem chromaticNumber_le_two_iff_isBipartite {V : Type*} {G : SimpleGraph V} :
    G.chromaticNumber ≤ 2 ↔ G.IsBipartite :=
  chromaticNumber_le_iff_colorable

/-- The chromatic number of a graph is at least 2 if and only if the graph is not empty -/
theorem chromaticNumber_eq_two_iff {V : Type*} {G : SimpleGraph V} :
    G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G ≠ ⊥ :=
  ⟨fun h ↦ ⟨chromaticNumber_le_two_iff_isBipartite.mp (by simp [h]),
            two_le_chromaticNumber_iff_ne_bot.mp (by simp [h])⟩,
   fun ⟨h₁, h₂⟩ ↦ ENat.eq_of_forall_natCast_le_iff fun _ ↦
      ⟨fun h ↦ h.trans <| chromaticNumber_le_two_iff_isBipartite.mpr h₁,
       fun h ↦ h.trans <| two_le_chromaticNumber_iff_ne_bot.mpr h₂⟩⟩

/-- Bicoloring of a path graph -/
def pathGraph.bicoloring (n : ℕ) :
    Coloring (pathGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

/-- Embedding of `pathGraph 2` into the first two elements of `pathGraph n` for `2 ≤ n` -/
def pathGraph_two_embedding (n : ℕ) (h : 2 ≤ n) : pathGraph 2 ↪g pathGraph n where
  toFun v := ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [pathGraph, ← Fin.coe_covBy_iff]

/-- The chromatic number of a path graph of size at least 2 is 2 -/
theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj

/-- A walk has even length if and only if its endpoints have the same color -/
theorem Coloring.even_length_iff_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Even p.length ↔ (c u ↔ c v) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff, ← Bool.eq_iff_iff]
      exact c.valid h
    tauto

/-- A walk has odd length if and only if its endpoints have different colors -/
theorem Coloring.odd_length_iff_not_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Odd p.length ↔ (¬c u ↔ c v) := by
  rw [← Nat.not_even_iff_odd, c.even_length_iff_congr p]
  tauto

/-- A graph containing an odd loop has chromatic number at least 3 -/
theorem Walk.three_le_chromaticNumber_of_odd_loop {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hOdd : Odd p.length) : 3 ≤ G.chromaticNumber := by
  by_contra h
  have h' : G.chromaticNumber ≤ 2 := Order.le_of_lt_add_one <| not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_congr p).mp hOdd
  simp_all

/-- Bicoloring of a cycle graph of even size -/
def cycleGraph.bicoloring_of_even (n : ℕ) (h : Even n) : Coloring (cycleGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hadj
      cases hadj with
      | inl huv | inr huv =>
        rw [← add_eq_of_eq_sub' huv.symm, ← Fin.even_iff_mod_of_even h,
          ← Fin.even_iff_mod_of_even h, Fin.even_add_one_iff_odd]
        apply Classical.not_iff.mpr
        simp [Fin.not_odd_iff_even_of_even h, Fin.not_even_iff_odd_of_even h]

/-- The chromatic number of a cycle graph of even size is 2 -/
theorem chromaticNumber_cycleGraph_of_even (n : ℕ) (h : 2 ≤ n) (hEven : Even n) :
    (cycleGraph n).chromaticNumber = 2 := by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

/-- Tricoloring of a cycle graph -/
def cycleGraph.tricoloring (n : ℕ) (h : 2 ≤ n) : Coloring (cycleGraph n)
    (Fin 3) := Coloring.mk (fun u ↦ if u.val = n - 1 then 2 else ⟨u.val % 2, by lia⟩) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only
      simp only [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hadj
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val (?_))).symm
        exact v.val.mod_lt Nat.zero_lt_two
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val ?_))
        exact u.val.mod_lt Nat.zero_lt_two
      · simp only [ne_eq, Fin.ext_iff]
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        cases hadj with
        | inl huv | inr huv =>
          rw [← add_eq_of_eq_sub' huv.symm]
          simp only [Fin.val_add_eq_of_add_lt hv', Fin.val_add_eq_of_add_lt hu', Fin.val_one]
          rw [show ∀ x y : ℕ, x % 2 = y % 2 ↔ (Even x ↔ Even y) by simp [Nat.even_iff]; lia,
            Nat.even_add]
          simp only [Nat.not_even_one, iff_false, not_iff_self, iff_not_self]
          exact id

/-- The chromatic number of a cycle graph of odd size is 3 -/
theorem chromaticNumber_cycleGraph_of_odd (n : ℕ) (h : 2 ≤ n) (hOdd : Odd n) :
    (cycleGraph n).chromaticNumber = 3 := by
  have hc := (cycleGraph.tricoloring n h).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hn3 : n - 3 + 3 = n := by
      refine Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h ?_))
      intro h2
      rw [← h2] at hOdd
      exact (Nat.not_odd_iff.mpr rfl) hOdd
    let w : (cycleGraph (n - 3 + 3)).Walk 0 0 := cycleGraph_EulerianCircuit (n - 3)
    have hOdd' : Odd w.length := by
      rw [cycleGraph_EulerianCircuit_length, hn3]
      exact hOdd
    rw [← hn3]
    exact Walk.three_le_chromaticNumber_of_odd_loop w hOdd'

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The injection `(x₁, x₂) ↦ x₁` is always an `r`-coloring of a `completeEquipartiteGraph r ·`. -/
def Coloring.completeEquipartiteGraph :
  (completeEquipartiteGraph r t).Coloring (Fin r) := ⟨Prod.fst, id⟩

/-- The `completeEquipartiteGraph r t` is always `r`-colorable. -/
theorem completeEquipartiteGraph_colorable :
  (completeEquipartiteGraph r t).Colorable r := ⟨Coloring.completeEquipartiteGraph⟩

end CompleteEquipartiteGraph

open Walk
/-- A simple graph is 2-colorable if and only if all its loops have even length -/
lemma two_colorable_iff_forall_loop_even {α : Type*} {G : SimpleGraph α} :
    G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), Even w.length := by
  simp_rw [← Nat.not_odd_iff_even]
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponents.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a ↦ Fin.ofNat 2 (c.connected_toSimpleGraph ⟨_, hv⟩ a).some.length
    intro a b hab he
    apply h _ <| (((c.connected_toSimpleGraph ⟨_, hv⟩ a).some.concat hab).append
                 (c.connected_toSimpleGraph ⟨_, hv⟩ b).some.reverse).map c.toSimpleGraph_hom
    rw [length_map, length_append, length_concat, length_reverse, add_right_comm]
    have : ((Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ a)).length) % 2 =
        (Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ b)).length % 2 := by
      simp_rw [← Fin.val_natCast, ← Fin.ofNat_eq_cast, he]
    exact (Nat.even_iff.mpr (by lia)).add_one

section OddCycleTheorem

variable {V : Type*} (G : SimpleGraph V)

/-- A graph is bipartite if and only if it does not contain an odd cycle -/
lemma Coloring.even_length_iff_same_color (c : G.Coloring (Fin 2)) {u v : V} (p : G.Walk u v) :
    Even p.length ↔ c u = c v := by
  let c' : G.Coloring Bool := G.recolorOfEquiv (finTwoEquiv : Fin 2 ≃ Bool) c
  rw [Coloring.even_length_iff_congr c']
  simp [c']

/-- The bypass of a walk is a path -/
@[simp]
lemma Walk.bypass_eq_nil
{V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V} (w : G.Walk u u) :
    w.bypass = Walk.nil :=
  (isPath_iff_eq_nil _).1 (Walk.bypass_isPath _)

/-- If all cycles in a graph have even length, then extending a path by an adjacent edge
    results in a walk of even length -/
theorem even_length_cons_of_isPath
    (h_cycles : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length)
    {u v : V} (q : G.Walk v u) (hq : q.IsPath) (ha : G.Adj u v) :
    Even (Walk.cons ha q).length := by
  by_cases hq' : q.length = 1
  · simp [hq']
  apply h_cycles u (Walk.cons ha q)
  rw [cons_isCycle_iff]
  refine ⟨hq, ?_⟩
  cases q
  · simp
  · rw [edges_cons, List.mem_cons]
    rintro (h | ha)
    · aesop
    · rw [cons_isPath_iff] at hq
      exact hq.2 <| snd_mem_support_of_mem_edges _ ha

/-- If a path between `u` and `v` contains the edge `{u, v}`, then the path has length 1. -/
lemma IsPath.length_eq_one_of_mem_edges
{u v : V} {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) ∈ p.edges) : p.length = 1 := by
  by_contra h_non_simple_cycle
  have h_cycle : ∃ q : G.Walk u u, q.IsCycle := by
    rcases p with (_ | ⟨_, _, p⟩)
    · aesop
    · aesop
    · aesop (config := {warnOnNonterminal := false})
      have := by exact Walk.fst_mem_support_of_mem_edges p h_3
      exact Classical.not_forall_not.mp fun a ↦ right this
  obtain ⟨q, hq⟩ := h_cycle
  cases q <;> simp_all +decide only [isCycle_def, IsTrail.nil, ne_eq, not_true_eq_false,
    support_nil, List.tail_cons, List.nodup_nil, and_true, and_false]
  cases p <;> simp_all +decide only [isTrail_def, edges_cons, List.nodup_cons, reduceCtorEq,
    not_false_eq_true, support_cons, List.tail_cons, true_and, isPath_iff_eq_nil, edges_nil,
    List.not_mem_nil]
  simp_all only [cons_isPath_iff, List.mem_cons, Sym2.eq, Sym2.rel_iff',
  Prod.mk.injEq, true_and, Prod.swap_prod_mk, length_cons, Nat.add_eq_right]
  obtain ⟨left, right⟩ := hq
  obtain ⟨left_1, right_1⟩ := hp
  obtain ⟨left, right_2⟩ := left
  cases h with
  | inl h_3 =>
    cases h_3 with
    | inl h =>
      subst h
      simp_all only [length_eq_zero_iff, isPath_iff_eq_nil]
    | inr h_4 => simp_all only [SimpleGraph.irrefl]
  | inr h_4 => exact right_1 (Walk.fst_mem_support_of_mem_edges _ h_4)

/-- If all cycles in a graph have even length, then extending a path by an adjacent edge
    and taking until a vertex `u` results in a walk of even length -/
lemma even_length_cons_takeUntil_of_bypass [DecidableEq V]
    {u v w : V} (q : G.Walk v w) (hq : q.IsPath) (ha : G.Adj u v) (hs : u ∈ q.support)
    (h_cycles : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) :
    Even (SimpleGraph.Walk.cons ha (q.takeUntil u hs)).length := by
  by_cases hc : SimpleGraph.Walk.IsCycle (SimpleGraph.Walk.cons ha (q.takeUntil u hs))
  · exact h_cycles _ _ hc
  · have h_edge : s(u, v) ∈ (q.takeUntil u hs).edges := by
      contrapose! hc; simp_all +decide only [cons_isCycle_iff, not_false_eq_true, and_true]
      exact IsPath.takeUntil hq hs
    have h_length : (q.takeUntil u hs).length = 1 := by
      apply IsPath.length_eq_one_of_mem_edges
      · exact hq.takeUntil _
      · rwa [Sym2.eq_swap]
    aesop

/-- If all cycles in a graph have even length, then a walk has even length -/
lemma even_length_iff_even_bypass_length [DecidableEq V]
    (h_cycles : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length)
    {u v : V} (p : G.Walk u v) :
    Even p.length ↔ Even p.bypass.length := by
  induction p with
  | nil =>
    simp_all only [Walk.length_nil, Even.zero, true_iff]
    exact even_iff_two_dvd.mpr ⟨0, rfl⟩
  | cons h p ih =>
    simp +decide [SimpleGraph.Walk.bypass]
    split_ifs <;> simp_all +decide [parity_simps]
    have h_even : Even (SimpleGraph.Walk.cons h (p.bypass.takeUntil _ ‹_›)).length := by
      apply even_length_cons_takeUntil_of_bypass
      · exact bypass_isPath p
      · assumption
    simp_all +decide [SimpleGraph.Walk.length_cons, parity_simps]
    have h_even :
        Even (SimpleGraph.Walk.length p.bypass) ↔
        Even (SimpleGraph.Walk.length (p.bypass.takeUntil _ ‹_›) +
              SimpleGraph.Walk.length (p.bypass.dropUntil _ ‹_›)) := by
      rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
    grind

/-- A graph is bipartite if and only if it does not contain an odd cycle -/
theorem bipartite_iff_all_cycles_even :
  G.IsBipartite ↔ ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length := by
  classical
  constructor
  · intro h_bip
    rcases h_bip with ⟨color⟩
    intro v c hc
    have h_color_eq : color v = color v := rfl
    rw [Coloring.even_length_iff_same_color]
    exact color
  · intro h
    have h_colorable : G.Colorable 2 := by
      apply (two_colorable_iff_forall_loop_even).mpr
      intro u w
      have h_even_bypass : Even w.length ↔ Even w.bypass.length := by
        apply even_length_iff_even_bypass_length
        assumption
      rw [h_even_bypass]
      rw [bypass_eq_nil]
      aesop
    exact Colorable.mono_left (fun ⦃v w⦄ a => a) h_colorable

/-- The same as `bipartite_iff_all_cycles_even`, but as a direct implication -/
theorem IsBipartite.of_no_odd_cycle
(h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) :
    G.IsBipartite := (bipartite_iff_all_cycles_even G).mpr h

end OddCycleTheorem

end SimpleGraph

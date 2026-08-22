/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Parity
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs.

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

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
  map_rel_iff' := by simp [pathGraph]

theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj

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

theorem Coloring.odd_length_iff_not_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Odd p.length ↔ (¬c u ↔ c v) := by
  rw [← Nat.not_even_iff_odd, c.even_length_iff_congr p]
  tauto

theorem Walk.three_le_chromaticNumber_of_odd_loop {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hOdd : Odd p.length) : 3 ≤ G.chromaticNumber := by
  by_contra! h
  have h' : G.chromaticNumber ≤ 2 := Order.le_of_lt_add_one h
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

theorem chromaticNumber_cycleGraph_of_even (n : ℕ) (h : 2 ≤ n) (hEven : Even n) :
    (cycleGraph n).chromaticNumber = 2 := by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

/-- Tricoloring of a cycle graph -/
def cycleGraph.tricoloring (n : ℕ) : Coloring (cycleGraph n) (Fin 3) :=
  .mk (fun u ↦ if u = n - 1 then 2 else ⟨u % 2, by lia⟩) fun {u v} hadj ↦ by
    match n with
    | 0 => exact u.elim0
    | 1 => exact absurd hadj cycleGraph_one_adj
    | n + 2 =>
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hadj
      · exact .symm <| Fin.ne_of_lt <| Fin.mk_lt_of_lt_val (v.val.mod_lt Nat.zero_lt_two :)
      · exact Fin.ne_of_lt <| Fin.mk_lt_of_lt_val (u.val.mod_lt Nat.zero_lt_two :)
      · have h2 (x y : ℕ) : x % 2 = y % 2 ↔ (x % 2 = 0 ↔ y % 2 = 0) := by lia
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        rcases hadj with huv | huv
        all_goals simp [← add_eq_of_eq_sub' huv.symm, h2, ← Nat.even_iff, Nat.even_add,
          Fin.val_add_eq_of_add_lt hv', Fin.val_add_eq_of_add_lt hu', -Nat.not_even_iff_odd]

theorem chromaticNumber_cycleGraph_of_odd (n : ℕ) (h : 2 ≤ n) (hOdd : Odd n) :
    (cycleGraph n).chromaticNumber = 3 := by
  apply cycleGraph.tricoloring n |>.colorable.chromaticNumber_le.antisymm
  have hn3 : n - 3 + 3 = n := by grind
  rw [Fintype.card_fin, Nat.cast_ofNat, ← hn3]
  apply cycleGraph.cycle (n - 3) |>.three_le_chromaticNumber_of_odd_loop
  rwa [cycleGraph.length_cycle, hn3]

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The injection `(x₁, x₂) ↦ x₁` is always an `r`-coloring of a `completeEquipartiteGraph r ·`. -/
def Coloring.completeEquipartiteGraph :
  (completeEquipartiteGraph r t).Coloring (Fin r) := ⟨Prod.fst, id⟩

/-- The `completeEquipartiteGraph r t` is always `r`-colorable. -/
theorem completeEquipartiteGraph_colorable :
  (completeEquipartiteGraph r t).Colorable r := ⟨Coloring.completeEquipartiteGraph⟩

end CompleteEquipartiteGraph

open Walk in
lemma isBipartite_iff_forall_walk_even_length {V : Type*} {G : SimpleGraph V} :
    G.IsBipartite ↔ ∀ (v : V) (p : G.Walk v v), Even p.length := by
  simp_rw [← Nat.not_odd_iff_even]
  refine ⟨fun h _ w ho ↦ ?_, fun h ↦ colorable_iff_forall_connectedComponent.mpr fun c ↦ ?_⟩
  · have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · have ⟨v, hv⟩ := c.nonempty_supp
    let f (u : c) := (c.connected_toSimpleGraph ⟨v, hv⟩ u).some
    refine ⟨fun u ↦ .ofNat 2 (f u).length, fun {a b} hab he ↦ ?_⟩
    apply h _ <| (((f a).concat hab).append (f b).reverse).map c.toSimpleGraph_hom
    rw [length_map, length_append, length_concat, length_reverse, Nat.odd_iff]
    have : (f a).length % 2 = (f b).length % 2 := by simpa using congr(($he : ℕ))
    lia

@[deprecated (since := "2026-08-12")]
alias two_colorable_iff_forall_loop_even := isBipartite_iff_forall_walk_even_length

end SimpleGraph

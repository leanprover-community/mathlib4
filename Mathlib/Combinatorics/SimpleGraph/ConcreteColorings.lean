/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Parity

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

assert_not_exists Field

namespace SimpleGraph

theorem two_le_chromaticNumber_of_adj {α} {G : SimpleGraph α} {u v : α} (hadj : G.Adj u v) :
    2 ≤ G.chromaticNumber := by
  refine le_of_not_gt ?_
  intro h
  have hc : G.Colorable 1 := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  let c : G.Coloring (Fin 1) := hc.some
  exact c.valid hadj (Subsingleton.elim (c u) (c v))

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
    (hOdd : Odd p.length) : 3 ≤ G.chromaticNumber := Classical.by_contradiction <| by
  intro h
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
  (Fin 3) := Coloring.mk (fun u ↦ if u.val = n - 1 then 2 else ⟨u.val % 2, by fin_omega⟩) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only
      simp [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hadj
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val (?_))).symm
        exact v.val.mod_lt Nat.zero_lt_two
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val ?_))
        exact u.val.mod_lt Nat.zero_lt_two
      · simp [Fin.ext_iff]
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        cases hadj with
        | inl huv | inr huv =>
          rw [← add_eq_of_eq_sub' huv.symm]
          simp only [Fin.val_add_eq_of_add_lt hv', Fin.val_add_eq_of_add_lt hu', Fin.val_one]
          rw [show ∀x y : ℕ, x % 2 = y % 2 ↔ (Even x ↔ Even y) by simp [Nat.even_iff]; omega,
            Nat.even_add]
          simp only [Nat.not_even_one, iff_false, not_iff_self, iff_not_self]
          exact id

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

end SimpleGraph

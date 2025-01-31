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

theorem two_le_chromaticNumber_of_adj {α} {G : SimpleGraph α} {u v : α} (hAdj : G.Adj u v) :
    2 ≤ G.chromaticNumber := by
  refine le_of_not_lt ?_
  intro h
  have hc : G.Colorable 1 := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  let c : G.Coloring (Fin 1) := hc.some
  exact c.valid hAdj (Subsingleton.elim (c u) (c v))

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
  · have hAdj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hAdj

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
    intro u v hAdj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hAdj
      cases hAdj with
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
  · have hAdj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hAdj

/-- Tricoloring of a cycle graph -/
def cycleGraph.tricoloring (n : ℕ) (h : 2 ≤ n) : Coloring (cycleGraph n)
  (Fin 3) := Coloring.mk (fun u ↦ if u.val = n - 1 then 2 else ⟨u.val % 2, by fin_omega⟩) <| by
    intro u v hAdj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only
      simp [cycleGraph_adj] at hAdj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hAdj
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val (?_))).symm
        exact v.val.mod_lt Nat.zero_lt_two
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val ?_))
        exact u.val.mod_lt Nat.zero_lt_two
      · simp [Fin.ext_iff]
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        cases hAdj with
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

--------- Greedy colorings
section degreeLT
variable {α : Type*} [LinearOrder α] (G : SimpleGraph α) (b : α)

def neighborSetLT  : Set α := {a | a < b ∧ G.Adj b a  }

variable [Fintype (G.neighborSetLT b)]

def neighborFinsetLT : Finset α := (G.neighborSetLT b).toFinset

def degreeLT : ℕ:= (G.neighborFinsetLT b).card

lemma mem_neighborFinsetLT  (a : α) : a ∈ G.neighborFinsetLT b ↔ a < b ∧ G.Adj b a :=
    Set.mem_toFinset

end degreeLT

variable (G : SimpleGraph ℕ) [DecidableRel G.Adj]

instance instFintypeNeighborLT: ∀ n, Fintype (G.neighborSetLT n) := by
  intro n
  apply Fintype.ofFinset ((Finset.range n).filter (G.Adj n))
  intro m; simp only [Finset.mem_filter, Finset.mem_range]
  rfl

open Finset
section DeltaLT
variable {Δ : ℕ} (hdeglt : ∀ n, G.degreeLT n ≤ Δ)
include hdeglt
lemma exists_col_unused (c : ℕ → Fin (Δ + 1)) (n : ℕ) :
    ((G.neighborFinsetLT n).image c)ᶜ.Nonempty := by
  apply (card_compl_lt_iff_nonempty _).1
  rw [compl_compl,Fintype.card_fin]
  apply Nat.succ_le_succ <| card_image_le.trans <| hdeglt _


private def col_unused (c : ℕ → Fin (Δ + 1)) (n : ℕ) : Fin (Δ + 1) :=
  min' _ (G.exists_col_unused hdeglt c n)

@[simp]
lemma col_unused_eq (c : ℕ → Fin (Δ + 1)) (n : ℕ) :
  G.col_unused hdeglt c n = min' _ (G.exists_col_unused hdeglt c n) := rfl

abbrev greedy (n : ℕ) : Fin (Δ + 1) :=
  G.col_unused hdeglt ((fun m ↦ ite (m < n) (greedy m) 0)) n

lemma greedy_def (n : ℕ) : G.greedy hdeglt n = min' _ (G.exists_col_unused hdeglt
  (fun m ↦ ite (m < n) (G.greedy hdeglt m) 0) n) := by rw [greedy]; simp

lemma greedy_not_mem (n : ℕ): G.greedy hdeglt n ∉ ((G.neighborFinsetLT n).image (fun m ↦ ite (m < n)
    (G.greedy hdeglt m) 0)) := by
  rw [greedy_def, ← mem_compl]
  exact min'_mem _ (G.exists_col_unused hdeglt (fun m ↦ ite (m < n) (G.greedy hdeglt m) 0) n)

lemma greedy_valid {m n : ℕ} (h : m < n) (hadj : G.Adj n m) :
    G.greedy hdeglt m ≠ G.greedy hdeglt n := by
  intro heq
  apply G.greedy_not_mem hdeglt n
  rw [mem_image]
  use m; rw [neighborFinsetLT,Set.mem_toFinset]
  use ⟨h,hadj⟩, if_pos h ▸ heq

def greedy_coloring : G.Coloring (Fin (Δ + 1)) :=by
  use (greedy G hdeglt)
  intro m n hadj
  by_cases h : m < n
  · apply G.greedy_valid hdeglt h hadj.symm
  · push_neg at h
    cases h.lt_or_eq with
    | inl hlt => rw [adj_comm]; apply G.greedy_valid hdeglt hlt hadj
    | inr heq => exfalso; apply G.loopless _ (heq ▸ hadj)

end DeltaLT
section bdddeg
variable {G} {Δ : ℕ} [LocallyFinite G] (hdeg : ∀ n, G.degree n ≤ Δ)
lemma degLT_le_degree (v : ℕ) : G.degreeLT v ≤ G.degree v := by
  rw [← card_neighborFinset_eq_degree, degreeLT]
  apply card_le_card
  intro m hm; rw [mem_neighborFinsetLT, mem_neighborFinset] at *
  exact hm.2

/-- If G is locally finite and all degrees are bounded above by Δ it is Δ + 1 colorable -/
def greedy_coloring_of_bdd_degree : G.Coloring (Fin (Δ + 1)) :=
  G.greedy_coloring (fun n ↦ (degLT_le_degree n).trans <| hdeg n)

end bdddeg
end SimpleGraph

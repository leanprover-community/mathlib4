/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.ZMod.Basic

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.
* `SimpleGraph.cycleGraph`: A graph forming exactly a cycle.

-/

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
  map_rel_iff' := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [pathGraph, ← Fin.coe_covBy_iff]

theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · simpa only [pathGraph_two_eq_top, chromaticNumber_top] using
      chromaticNumber_mono_of_embedding (pathGraph_two_embedding n h)

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
  rw [Nat.odd_iff_not_even, c.even_length_iff_congr p]
  tauto

/-- Definition of cycle graph -/
def cycleGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v ↦ v.val = (u.val + 1) % n)

theorem cycleGraph_adj (n : ℕ) (hn : 2 ≤ n) (u v : Fin n) :
    (cycleGraph n).Adj u v ↔ v.val = (u.val + 1) % n ∨ u.val = (v.val + 1) % n := by
  simp [cycleGraph]
  intro h
  wlog hvu : v.val = (u.val + 1) % n
  · rw [eq_comm]
    exact this n hn v u h.symm (h.resolve_left hvu)
  rw [Fin.ext_iff, hvu]
  apply_fun ((↑) : _ →  ZMod n)
  have : NeZero (1 : ZMod n) := @NeZero.one _ _ <| @ZMod.nontrivial n ⟨hn⟩
  simpa only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_one, ne_eq, self_eq_add_right] using
    one_ne_zero

/-- Bicoloring of a cycle graph of even length -/
def cycleGraph.bicoloring (n : ℕ) (h : 2 ≤ n) (hn : Even n) : Coloring (cycleGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v hAdj
    rw [cycleGraph_adj] at hAdj
    simp only [ne_eq, decide_eq_decide]
    wlog hvu : v.val = (u.val + 1) % n
    · rw [iff_comm]
      exact this n h hn hAdj.symm (hAdj.resolve_left hvu)
    rw [hvu, Nat.mod_mod_of_dvd (u.val + 1) (even_iff_two_dvd.mp hn)]
    omega
    exact h

/-- Tricoloring of a cycle graph -/
def cycleGraph.tricoloring  (n : ℕ) (h : 2 ≤ n) : Coloring (cycleGraph n) (Fin 3) :=
  Coloring.mk (fun u ↦ if u.val = n - 1 then 2 else ⟨u.val % 2, by omega⟩) <| by
    intro u v hAdj
    rw [cycleGraph_adj n h] at hAdj
    simp only [ne_eq]
    wlog hvu : v.val = (u.val + 1) % n
    · rw [eq_comm]
      exact this n h hAdj.symm (hAdj.resolve_left hvu)
    rw [hvu]
    have hu : u.val = n - 1 ∨ u.val < n - 1 := (Nat.le_sub_one_of_lt u.isLt).eq_or_lt
    match hu with
    | Or.inl hu =>
      simp only [hu, reduceIte, Nat.sub_add_cancel (Nat.one_le_of_lt h), Nat.mod_self,
        (Nat.sub_ne_zero_of_lt h).symm, Fin.ext_iff]
      omega
    | Or.inr hu =>
      simp only [hu.ne]
      have hu' : u.val = n - 2 ∨ u.val < n - 2 := (Nat.le_sub_one_of_lt hu).eq_or_lt
      match hu' with
      | Or.inl hu =>
        simp only [hu, reduceIte,
          (Nat.pred_eq_succ_iff.mpr (((Nat.sub_eq_iff_eq_add h).mp) rfl)).symm,
          Nat.mod_eq_of_lt (Nat.sub_one_lt_of_lt h), Fin.ext_iff]
        omega
      | Or.inr hu =>
        simp only [reduceIte,
          (u.val + 1).mod_eq_of_lt (Nat.add_lt_of_lt_sub (Nat.lt_of_lt_pred hu)),
          (@Nat.add_lt_of_lt_sub u.val 1 (n - 1) hu).ne, Fin.ext_iff]
        omega

end SimpleGraph

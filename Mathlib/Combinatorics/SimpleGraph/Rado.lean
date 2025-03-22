/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.ModEq

/-!
# Universal graphs and the Rado graph

The Rado graph is a countably infinite undirected graph with several special properties that can be
defined in a number of ways:
* the graph over `ℕ` induced by `testBit`, which is adopted here
* the graph over primes congruent to 1 mod 4 induced by quadratic reciprocity
* the almost sure result of the Erdős–Rényi random graph model

All these constructions are equivalent by the _extension property_: for any two disjoint vertex sets
we can find another vertex adjacent to all vertices in one set and none in the other.
Graphs with this property on a countably infinite vertex set are called _universal_.

In this file we first formalise `IsUniversal` and prove two properties about such graphs:
* `???`: any graph on finitely or countably infinitely many vertices is an induced subgraph.
* `???`: any two universal graphs are isomorphic.

Then we define `SimpleGraph.radoGraph` using `testBit` and prove that it is universal itself.

## References

* https://en.wikipedia.org/wiki/Rado_graph
-/

open Finset Nat

namespace SimpleGraph

section Universal

variable {V : Type*} [DecidableEq V]

/-- A universal graph is a graph on countably infinitely many vertices with
the extension property. -/
structure IsUniversal (G : SimpleGraph V) : Prop where
  /-- `G`'s vertex set is countably infinite. -/
  countable : Nonempty (V ≃ ℕ)
  /-- The extension property. Given two disjoint vertex finsets `A, B`
  there exists another vertex adjacent to everything in `A` and nothing in `B`. -/
  ext_prop {A B : Finset V} (h : Disjoint A B) :
    ∃ x ∉ A ∪ B, ↑A ⊆ G.neighborSet x ∧ Disjoint (G.neighborSet x) B

variable {G : SimpleGraph V} (h : G.IsUniversal)

/- Any graph over `ℕ` embeds in a universal graph.
lemma IsUniversal.nonempty_embedding (H : SimpleGraph ℕ) [DecidableRel H.Adj] :
    Nonempty (H ↪g G) := by
  sorry

Any graph over `Fin n` embeds in a universal graph.
lemma IsUniversal.nonempty_embedding_fin {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Nonempty (H ↪g G) := by
  sorry
  induction n with
  | zero => use Fin.valEmbedding; intro a b; have := a.2; tauto
  | succ n ih =>
    let H := G.comap Fin.castSucc
    obtain ⟨f, hf⟩ := ih H
    let A : Finset (Fin n) := univ.filter (fun i ↦ G.Adj (Fin.last n) i.castSucc)
    have dj : Disjoint (A.map Fin.valEmbedding) (Aᶜ.map Fin.valEmbedding) := by
      rw [disjoint_map]
      apply disjoint_compl_right
    obtain ⟨s, hs₀, hs₁, hs₂⟩ := radoGraph_isUniversal.ext_prop dj
    let g : Fin (n + 1) → ℕ := Fin.lastCases s f
    have ginj : g.Injective := fun i j h ↦ by
      obtain hi | hi := eq_or_ne i (Fin.last n) <;>
      obtain hj | hj := eq_or_ne j (Fin.last n)
      · rw [hi, hj]
      · sorry
      · sorry
      · sorry
    use ⟨g, ginj⟩
    intro i j
    simp only [g, Function.Embedding.coeFn_mk]
    sorry-/

end Universal

/-- The Rado graph defined using `testBit`. -/
def radoGraph : SimpleGraph ℕ where
  Adj x y := x.testBit y || y.testBit x
  loopless x := by rw [Bool.not_eq_true, Bool.or_self, testBit_eq_false_of_lt (lt_two_pow x)]

instance : DecidableRel radoGraph.Adj := by dsimp only [radoGraph]; infer_instance

lemma testBit_sum_two_pow {U : Finset ℕ} {u : ℕ} : (∑ i ∈ U, 2 ^ i).testBit u ↔ u ∈ U := by
  rw [testBit_to_div_mod, decide_eq_true_eq]
  have fd : ∀ i ∈ filter (fun x ↦ ¬x < u) U, 2 ^ u ∣ 2 ^ i := fun a ma ↦ by
    refine pow_dvd_pow 2 ?_
    rw [mem_filter, not_lt] at ma
    exact ma.2
  rw [← sum_filter_add_sum_filter_not (p := (· < u)), Nat.add_div_of_dvd_left (dvd_sum fd),
    Nat.sum_div fd]
  have fe : U.filter (· < u) = (range u).filter (· ∈ U) := by
    ext; simp_rw [mem_filter, mem_range, and_comm]
  have fl : ∑ x ∈ (range u).filter (· ∈ U), 2 ^ x < 2 ^ u :=
    calc
      _ ≤ ∑ x ∈ range u, 2 ^ x := sum_le_sum_of_subset (filter_subset ..)
      _ < _ := geomSum_lt le_rfl (by simp)
  rw [fe, div_eq_of_lt fl, zero_add, ← sum_filter_add_sum_filter_not (p := (· > u))]
  have c₁ : (U.filter (¬· < u)).filter (· > u) = U.filter (u < ·) := by
    ext
    simp only [gt_iff_lt, not_lt, mem_filter, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.le
  have c₂ : ∀ x ∈ U.filter (u < ·), 2 ^ x / 2 ^ u = 2 * (2 ^ (x - u - 1)) := fun x mx ↦ by
    rw [mem_filter] at mx
    rw [← _root_.pow_succ', show x - u - 1 + 1 = x - u by omega]
    exact Nat.pow_div mx.2.le zero_lt_two
  rw [sum_congr c₁ c₂, ← mul_sum, mul_add_mod]
  have c₃ : (U.filter (¬· < u)).filter (¬· > u) = (U.filter (· = u)) := by
    ext
    simp_rw [mem_filter, not_lt, and_assoc, and_congr_right_iff]
    exact fun _ ↦ by rw [eq_comm]; exact le_antisymm_iff.symm
  rw [c₃, filter_eq']
  split_ifs with h <;> simp [h]

/-- The Rado graph is universal. -/
theorem radoGraph_isUniversal : radoGraph.IsUniversal where
  countable := ⟨Equiv.refl ℕ⟩
  ext_prop {U V} h := by
    by_cases h' : (U ∪ V).Nonempty
    · obtain ⟨k, hk⟩ := max_of_nonempty h'
      have wl : ∀ {w}, w ∈ U ∪ V → w < k + 1 := fun {w} mw ↦
        lt_add_one_of_le (by exact_mod_cast hk ▸ le_max mw)
      use ∑ i ∈ insert (k + 1) U, 2 ^ i
      refine ⟨?_, fun u hu ↦ ?_, ?_⟩
      · apply not_mem_of_max_lt_coe
        rw [hk, WithBot.coe_lt_coe]
        calc
          k < k + 1 := by omega
          _ < 2 ^ (k + 1) := lt_two_pow _
          _ ≤ _ := single_le_sum (by simp) (mem_insert_self ..)
      · simp_rw [mem_neighborSet, radoGraph, Bool.or_eq_true]
        left
        rw [testBit_sum_two_pow, mem_insert]
        tauto
      · rw [Set.disjoint_right]
        intro v hv
        have vl : v < k + 1 := wl (mem_union.mpr (Or.inr hv))
        simp_rw [mem_neighborSet, radoGraph, Bool.not_eq_true, Bool.or_eq_false_iff]
        constructor
        · rw [Bool.eq_false_iff, ne_eq, testBit_sum_two_pow, mem_insert, not_or]
          exact ⟨vl.ne, by rw [disjoint_right] at h; exact h hv⟩
        · apply testBit_lt_two_pow
          calc
            _ < 2 ^ v := lt_two_pow v
            _ < 2 ^ (k + 1) := by rwa [pow_lt_pow_iff_right one_lt_two]
            _ ≤ ∑ i ∈ insert (k + 1) U, 2 ^ i := single_le_sum (by simp) (mem_insert_self ..)
            _ < _ := lt_two_pow _
    · rw [not_nonempty_iff_eq_empty, union_eq_empty] at h'
      simp [h']

end SimpleGraph

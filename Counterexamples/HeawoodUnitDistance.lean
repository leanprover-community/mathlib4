/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic

/-!
# A simple planar unit-distance embedding of the Heawood graph

The Heawood graph on 14 vertices is the point-line incidence graph of the Fano plane.
Besides being 3-regular and symmetric it has a number of interesting properties:
it is the unique (3,6)-cage, it can be embedded on the torus with dual `K₇` and so on.

In 1972 Chvátal wrote of a "suspicion" that the Heawood graph was not unit-distance embeddable
into the Euclidean plane (Problem 21 in [chvatal1972]). In 2009 Gerbracht disproved the suspicion
by presenting an explicit embedding [gerbracht2009], but the embeddings presented there are
very hard to describe: the minimal polynomials of their vertex coordinates go up to degree 79.
Other embeddings found since then, such as the one in [hong2014], suffer from the same
complexity issue.

This file formalises a much simpler embedding, independently found by Moritz Firsching [in July 2016](https://mathoverflow.net/q/244604)
and Jeremy Tan [in August 2025](https://github.com/Parcly-Taxel/Shibuya/commit/b5c86cbf1c8b2e1211b160f266480e7115a7e43a).
Its coordinates are polynomials in the unique real root of `2c^3 + 3c + 1`.
-/

namespace SimpleGraph

open Finset

/-- The Heawood graph, a notable simple graph on 14 vertices. The numbering corresponds to a
typical [Hamiltonian cycle-and-arcs drawing](https://commons.wikimedia.org/wiki/File:Heawood_Graph.svg). -/
def heawoodGraph : SimpleGraph (Fin 14) where
  Adj i j := (i - j).1 = 1            ∨ (j - i).1 = 1 ∨
             (i - j).1 = 5 ∧ Even j.1 ∨ (j - i).1 = 5 ∧ Even i.1
  symm i j := by grind

instance : DecidableRel heawoodGraph.Adj :=
  inferInstanceAs <| DecidableRel fun (i j : Fin 14) ↦
    (i - j).1 = 1 ∨ (j - i).1 = 1 ∨ (i - j).1 = 5 ∧ Even j.1 ∨ (j - i).1 = 5 ∧ Even i.1

lemma heawoodGraph_edgeFinset :
    heawoodGraph.edgeFinset = (univ.image fun i ↦ s(i, i + 1)) ∪
      (univ.filter (Even ·.1)).image fun i ↦ s(i, i + 5) := by
  decide +kernel

lemma card_heawoodGraph_edgeFinset : #heawoodGraph.edgeFinset = 21 := by
  rw [heawoodGraph_edgeFinset]; decide

lemma heawoodGraph_neighborFinset (i : Fin 14) :
    heawoodGraph.neighborFinset i = {i + 1, i - 1, if Even i.1 then i + 5 else i - 5} := by
  revert i; decide +kernel

/-- The Heawood graph is 3-regular. -/
lemma isRegularOfDegree_heawoodGraph : heawoodGraph.IsRegularOfDegree 3 := fun i ↦ by
  rw [← card_neighborFinset_eq_degree, heawoodGraph_neighborFinset]; revert i; decide

/-! ### A key number -/

namespace Heawood

/-- `2c^3+3c+1` has a root in `(-1/3, -5/16)`. This root, which turns out to be unique
(we do not need uniqueness), underpins our unit-distance embedding's coordinates. -/
lemma exists_root_in_Ioo :
    ∃ c ∈ Set.Ioo (-1 / 3 : ℝ) (-5 / 16), 2 * c ^ 3 + 3 * c + 1 = 0 :=
  intermediate_value_Ioo (by norm_num) (by fun_prop) (by norm_num)

/-- The real root `c = -0.312908...` of `2c^3+3c+1`. -/
noncomputable def root : ℝ :=
  exists_root_in_Ioo.choose

@[inherit_doc] scoped notation "c" => root

lemma root_bounds : c ∈ Set.Ioo (-1 / 3) (-5 / 16) :=
  exists_root_in_Ioo.choose_spec.1

lemma root_equation : 2 * c ^ 3 + 3 * c + 1 = 0 :=
  exists_root_in_Ioo.choose_spec.2

/-! ### The embedding proper -/

/-- Notation for the Euclidean plane. -/
notation "Plane" => EuclideanSpace ℝ (Fin 2)

lemma dist_eq_one_iff {x₀ y₀ x₁ y₁ : ℝ} :
    dist !₂[x₀, y₀] !₂[x₁, y₁] = 1 ↔ (x₀ - x₁) ^ 2 + (y₀ - y₁) ^ 2 = 1 := by
  simp [dist_eq_norm_sub, PiLp.norm_eq_of_L2]

/-- The base function from graph vertices to Euclidean points in our embedding. -/
noncomputable def udMap : Fin 14 → Plane
  | 1 => !₂[(1 + c) / 2, c ^ 2 - c / 2 + 1]
  | 0 => !₂[c, 1 / 2] | 7 => !₂[0, 1 / 2] | 2 => !₂[1, 1 / 2] | 9 => !₂[1 - c, 1 / 2]
  | 10 => !₂[(1 + c) / 2, c ^ 2 - c / 2] | 5 => !₂[(1 - c) / 2, c ^ 2 - c / 2]
  | 3 => !₂[(1 + c) / 2, -(c ^ 2 - c / 2)] | 8 => !₂[(1 - c) / 2, -(c ^ 2 - c / 2)]
  | 13 => !₂[c, -1 / 2] | 6 => !₂[0, -1 / 2] | 11 => !₂[1, -1 / 2] | 4 => !₂[1 - c, -1 / 2]
  | 12 => !₂[(1 + c) / 2, -(c ^ 2 - c / 2 + 1)]

lemma reflect_toEuclideanLin {x y : ℝ} : !![1, 0; 0, -1].toEuclideanLin !₂[x, y] = !₂[x, -y] := by
  ext i; match i with | 0 => simp | 1 => simp

lemma udMap_reflect (i : Fin 14) : udMap i.rev = !![1, 0; 0, -1].toEuclideanLin (udMap i) := by
  fin_cases i <;> simp only [udMap, reflect_toEuclideanLin, Fin.reduceFinMk, Fin.reduceRev] <;>
  norm_num

lemma decompose_point (p : Plane) : p = !₂[p.proj 0, p.proj 1] := by
  ext i; match i with | 0 => simp | 1 => simp

/-- `udMap` is injective on indices `[0, 7, 10, 5, 2, 9]` because their x-coordinates
strictly increase in that order. -/
lemma injOn_udMap_sextet : Set.InjOn udMap ({0, 7, 10, 5, 2, 9} : Finset (Fin 14)) := by
  let f : Fin 6 → Fin 14 := ![0, 7, 10, 5, 2, 9]
  have frange : Set.range f = ({0, 7, 10, 5, 2, 9} : Finset (Fin 14)) := by
    rw [Set.range_eq_iff]; decide
  suffices StrictMono fun n ↦ (udMap (f n)).proj 0 by
    intro i mi j mj h
    rw [← frange, Set.mem_range] at mi mj
    obtain ⟨ci, hci⟩ := mi
    obtain ⟨cj, hcj⟩ := mj
    rw [← hci, ← hcj] at h
    apply_fun (·.proj 0) at h
    rwa [← hci, this.injective h]
  rw [Fin.strictMono_iff_lt_succ]
  obtain ⟨lb, ub⟩ := root_bounds
  simp [Fin.forall_fin_succ, f, udMap]
  grind

/-- `udMap` is injective and thus can be used in a unit-distance embedding. -/
theorem injective_udMap : udMap.Injective := by
  let s : Finset (Fin 14) := {1, 0, 7, 10, 5, 2, 9}
  have rev_compl (i) : i ∈ s ↔ i.rev ∉ s := by revert i; decide +kernel
  suffices (∀ i ∈ s, 0 < (udMap i).proj 1) ∧ Set.InjOn udMap s by
    obtain ⟨hpos, hinjOn⟩ := this
    have hneg (i) (ni : i ∉ s) : (udMap i).proj 1 < 0 := by
      rw [← Fin.rev_rev i, ← rev_compl] at ni
      specialize hpos _ ni
      rw [udMap_reflect] at hpos
      rw [decompose_point (udMap i)] at hpos ⊢
      simpa using hpos
    intro i j hij
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · exact hinjOn hi hj hij
    · exact absurd (hij ▸ hneg _ hj) (lt_asymm (hpos _ hi))
    · exact absurd (hij ▸ hneg _ hi) (lt_asymm (hpos _ hj))
    · rw [← Fin.rev_rev i, ← rev_compl] at hi
      rw [← Fin.rev_rev j, ← rev_compl] at hj
      simpa [udMap_reflect, hij] using hinjOn hi hj
  obtain ⟨lb, ub⟩ := root_bounds
  refine ⟨?_, ?_⟩
  · simp [s, udMap]
    constructor <;> nlinarith
  rw [coe_insert, Set.injOn_insert (by decide)]
  refine ⟨injOn_udMap_sextet, ?_⟩
  simp_rw [Set.mem_image, not_exists, not_and, mem_coe, PiLp.ext_iff, not_forall]
  intro i mi
  use 1
  revert i
  simp [udMap]
  nlinarith

lemma dist_udMap_rev {i j : Fin 14} (h : dist (udMap i) (udMap j) = 1) :
    dist (udMap i.rev) (udMap j.rev) = 1 := by
  rw [decompose_point (udMap i), decompose_point (udMap j), dist_eq_one_iff] at h
  rw [udMap_reflect, decompose_point (udMap i), reflect_toEuclideanLin,
    udMap_reflect, decompose_point (udMap j), reflect_toEuclideanLin, dist_eq_one_iff]
  linarith

lemma dist_udMap_rev_iff {i j : Fin 14} :
    dist (udMap i) (udMap j) = 1 ↔ dist (udMap i.rev) (udMap j.rev) = 1 where
  mp := dist_udMap_rev
  mpr h := by rw [← Fin.rev_rev i, ← Fin.rev_rev j]; exact dist_udMap_rev h

lemma dist_udMap_eq_one_of_eq
    {i j i' j' : Fin 14} (he : s(i', j') = s(i, j)) (hd : dist (udMap i') (udMap j') = 1) :
    dist (udMap i) (udMap j) = 1 := by
  rw [Sym2.eq_iff] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hd
  · rwa [dist_comm]

/-- A unit-distance embedding of the Heawood graph in the Euclidean plane. -/
noncomputable def unitDistEmbedding : heawoodGraph.UnitDistEmbedding Plane where
  p := ⟨udMap, injective_udMap⟩
  unit_dist {i j} h := by
    simp only [Function.Embedding.coeFn_mk]
    simp_rw [← mem_edgeSet, ← mem_edgeFinset, heawoodGraph_edgeFinset, mem_union, mem_image,
      mem_univ, true_and] at h
    rcases h with ⟨k, hk⟩ | ⟨k, mk, hk⟩ <;> apply dist_udMap_eq_one_of_eq hk <;> clear! i j
    · wlog hk : 6 ≤ k
      · have sixl : 6 ≤ k.rev - 1 := by revert k; decide
        have rae : k.rev - 1 = (k + 1).rev := by revert k; decide
        specialize this _ sixl
        rwa [sub_add_cancel, rae, ← dist_udMap_rev_iff, dist_comm] at this
      replace hk : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by
        revert k; decide
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [udMap, Fin.reduceAdd, Fin.isValue, dist_eq_one_iff]
        grind [root_equation]
    · replace mk : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨ k = 12 := by
        revert k; decide
      rcases mk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [udMap, Fin.reduceAdd, Fin.isValue, dist_eq_one_iff]
        grind [root_equation]

end Heawood

end SimpleGraph

/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Combinatorics.Graph.Basic

/-!
# Definitions of degrees

This file defines the degree of a vertex, both as a term in `ℕ∞` and as a term in `ℕ`.

## Main definitions

- `incFun`: `ℕ`-valued function counting how many times an edge is incident to a vertex. For a fixed
  `e`, `x`, `G.incFun e x` is 0 if `e` is not incident to `x`, 1 if `e` is a nonloop edge at `x`
  and 2 if `e` is a loop edge at `x`.
- `eDegree`: the degree of a vertex as a term in `ℕ∞`
- `degree`: the degree of a vertex as a term in `ℕ`

-/

public section

open Function Set

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β}

namespace Graph

@[simp, grind! .]
lemma endPoint_encard_le_two (G : Graph α β) (e : β) : (G.endPoint e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heE
    rw [h.endPoint_eq]
    by_cases hxy : x = y <;> simp [hxy, encard_pair]
  simp [endPoint_eq_of_notMem heE]

@[simp]
lemma subsingleton_setOf_isLink (G : Graph α β) (e : β) (x : α) :
    {y | G.IsLink e x y}.Subsingleton := by
  simp only [Set.Subsingleton, mem_setOf_eq]
  exact fun y hy z hz ↦ hy.right_unique hz

@[simp]
lemma endPoint_finite (G : Graph α β) (e : β) : (G.endPoint e).Finite :=
  finite_of_encard_le_coe <| G.endPoint_encard_le_two e

/-- The 'incidence function' of a graph `G`. If `e : β` and `x : α`,
then `G.incFun e x` is equal to `0` if `e` is not incident to `x`,
`1` if `e` is a nonloop edge at `x` and `2` if `e` is a loop edge at `x`.
It is defined this way so that `G.incFun e` sums to two for each `e ∈ E(G)`,
which is natural for the handshake theorem and linear algebra on graphs.

The definition is contrivedly written in terms of `ncard` so it
does not require any explicit decidability assumptions. -/
noncomputable def incFun (G : Graph α β) (e : β) : α →₀ ℕ where
  support := (G.endPoint_finite e).toFinset
  toFun x := {y | G.IsLink e x y}.ncard + ({y | G.IsLink e x y} ∩ {x}).ncard
  mem_support_toFun x := by
    obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
    · simp [hy.isLink_iff_eq, hy.inc_left]
    simp [hx, isLink_iff_inc]

lemma IsLink.incFun_support_eq [DecidableEq α] (h : G.IsLink e x y) :
    (G.incFun e).support = {x, y} := by
  simp [incFun, h.endPoint_eq]

lemma incFun_eq_zero_of_notMem (he : e ∉ E(G)) : G.incFun e = 0 := by
  simp [DFunLike.ext_iff, incFun, not_isLink_of_notMem_edgeSet he]

lemma incFun_le_two (G : Graph α β) (e : β) (x : α) : G.incFun e x ≤ 2 := by
  obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
  · suffices 1 + _ ≤ 2 by simpa [incFun, hy.isLink_iff_eq]
    have := ncard_singleton_inter y {x}
    omega
  simp [incFun, isLink_iff_inc, hx]

@[simp]
lemma incFun_eq_one_iff : G.incFun e x = 1 ↔ G.IsNonloopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · simp [incFun, hxy.isLink_iff_eq, IsNonloopAt, toFinite ({y} ∩ {x}), eq_comm (a := x)]
  simp [incFun, mt IsLink.inc_left hex, mt IsNonloopAt.inc hex]
alias ⟨_, IsNonloopAt.incFun_eq_one⟩ := incFun_eq_one_iff

@[simp]
lemma incFun_eq_two_iff : G.incFun e x = 2 ↔ G.IsLoopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · suffices 1 + _ = 2 ↔ x = y by simpa [incFun, hxy.isLink_iff_eq, ← isLink_self_iff]
    obtain rfl | hne := eq_or_ne y x
    · simp
    simp [(show Disjoint {y} {x} by simpa).inter_eq, hne.symm]
  simp [incFun, mt IsLink.inc_left hex, mt IsLoopAt.inc hex]
alias ⟨_, IsLoopAt.incFun_eq_two⟩ := incFun_eq_two_iff

lemma Inc.incFun_ne_zero (h : G.Inc e x) : G.incFun e x ≠ 0 := by
  obtain h | h := h.isLoopAt_or_isNonloopAt
  · simp [h.incFun_eq_two]
  simp [h.incFun_eq_one]

lemma Inc.one_le_incFun (h : G.Inc e x) : 1 ≤ G.incFun e x := by
  rw [Nat.one_le_iff_ne_zero]
  exact h.incFun_ne_zero

@[simp]
lemma incFun_eq_zero_iff : G.incFun e = 0 ↔ e ∉ E(G) := by
  refine ⟨fun h he ↦ ?_, incFun_eq_zero_of_notMem⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain hx | hx := hxy.inc_left.isLoopAt_or_isNonloopAt
  · have := h ▸ hx.incFun_eq_two
    simp at this
  have := h ▸ hx.incFun_eq_one
  simp at this

lemma sum_incFun_eq_two (he : e ∈ E(G)) : (G.incFun e).sum (fun _ x ↦ x) = 2 := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain rfl | hne := eq_or_ne x y
  · simpa [Finsupp.sum, hxy.incFun_support_eq, ← isLink_self_iff]
  simp only [Finsupp.sum, hxy.incFun_support_eq, Finset.sum_pair hne]
  rw [incFun_eq_one_iff.2 ⟨x, hne, hxy.symm⟩, incFun_eq_one_iff.2 ⟨y, hne.symm, hxy⟩]

@[simp]
lemma incFun_vertex_eq_zero_iff : G.incFun e x = 0 ↔ ¬ G.Inc e x := by
  refine ⟨fun h hinc ↦ hinc.incFun_ne_zero h, fun h ↦ ?_⟩
  simp only [incFun, Finsupp.coe_mk, Nat.add_eq_zero_iff]
  have hrw y : ¬ G.IsLink e x y := mt IsLink.inc_left h
  simp [hrw]

/-! ### Vertex Degrees -/

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, G.incFun e v

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

lemma eDegree_eq_tsum_mem : G.eDegree x = ∑' e : G.incidenceSet x, (G.incFun e x : ℕ∞) :=
  symm <| tsum_subtype_eq_of_support_subset (f := fun e ↦ (G.incFun e x : ℕ∞)) <| by simp

end Graph

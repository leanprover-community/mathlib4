/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot
-/

import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.LocalExtr

/-!
# Local maxima from monotonicity and antitonicity

In this file we prove a lemma that is useful for the First Derivative Test in calculus,
and its dual.

## Main statements

* `isLocalMax_of_mono_anti` : if a function `f` is monotone to the left of `x`
  and antitone to the right of `x` then `f` has a local maximum at `x`.

* `isLocalMin_of_anti_mono` : the dual statement for minima.

* `isLocalMax_of_mono_anti'` : a version of `isLocalMax_of_mono_anti` for filters.

* `isLocalMin_of_anti_mono'` : a version of `isLocalMax_of_mono_anti'` for minima.

-/

open Set Topology Filter

/-- If `f` is monotone on `(a,b]` and antitone on `[b,c)` then `f` has
a local maximum at `b`. -/
lemma isLocalMax_of_mono_anti.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b :=
  mem_of_superset (Ioo_mem_nhds g₀ g₁) (fun x _ => by rcases le_total x b <;> aesop)

/-- If `f` is antitone on `(a,b]` and monotone on `[b,c)` then `f` has
a local minimum at `b`. -/
lemma isLocalMin_of_anti_mono.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b :=
  mem_of_superset (Ioo_mem_nhds g₀ g₁) (fun x hx => by rcases le_total x b  <;> aesop)

/-- If `L` and `R` are neighborhoods of `b` within sets whose union is `Set.univ`, then
`L ∪ R` is a neighborhood of `b`. -/
theorem union_mem_nhds_of_mem_nhdsWithin.{u} {α : Type u} [TopologicalSpace α] {b : α}
    {I₁ I₂ : Set α} (h : ∀ x, x ∈ I₁ ∪ I₂)
    {L : Set α} (hL : L ∈ nhdsWithin b I₁)
    {R : Set α} (hR : R ∈ nhdsWithin b I₂) : L ∪ R ∈ nhds b := by
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hL with ⟨s, s_in, sL⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hR with ⟨t, t_in, tR⟩
  apply mem_of_superset (inter_mem s_in t_in)
  refine fun ⦃x⦄ hx ↦ (h x).elim ?_ ?_ <;> aesop

/-- Obtain a "predictably-sided" neighborhood of `b` from two one-sided neighborhoods. -/
theorem nhds_of_Ici_Iic.{u} {α : Type u} [TopologicalSpace α] [LinearOrder α] {b : α}
    {L : Set α} (hL : L ∈ 𝓝[≤] b)
    {R : Set α} (hR : R ∈ 𝓝[≥] b) : L ∩ Iic b ∪ R ∩ Ici b ∈ 𝓝 b :=
  union_mem_nhds_of_mem_nhdsWithin (fun x => le_total x b)
    (inter_mem hL self_mem_nhdsWithin) (inter_mem hR self_mem_nhdsWithin)

/-- If `f` is monotone to the left and antitone to the right, then it has a local maximum. -/
lemma isLocalMax_of_mono_anti'.{u, v} {α : Type u} [TopologicalSpace α] [LinearOrder α]
    {β : Type v} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : MonotoneOn f a) (h₁ : AntitoneOn f c) : IsLocalMax f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

/-- If `f` is antitone to the left and monotone to the right, then it has a local minimum. -/
lemma isLocalMin_of_anti_mono'.{u, v} {α : Type u} [TopologicalSpace α] [LinearOrder α]
    {β : Type v} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : AntitoneOn f a) (h₁ : MonotoneOn f c) : IsLocalMin f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, Patrick Massot
-/

import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.LeftRightNhds
/-!
# Local maxima from monotonicity and antitonicityOrder-closed topologies

In this file we prove a lemma that is useful for the First Derivative Test in calculus,
and its dual.

## Main statements

* `isLocalMax_of_mono_anti` : if a function `f` is monotone to the left of `x`
  and antitone to the right of `x` then `f` has a local maximum at `x`.

* `isLocalMin_of_anti_mono` : the dual statement for minima.

* `isLocalMax_of_mono_anti'` : a version of `isLocalMax_of_mono_anti` for filters.
-/

open Set Topology

/-- If `f` is monotone on `(a,b]` and antitone on `[b,c)` then `f` has
a local maximum at `b`. -/
lemma isLocalMax_of_mono_anti.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b :=
  Filter.mem_of_superset (Ioo_mem_nhds g₀ g₁) (fun x _ => by rcases le_total x b <;> aesop)

/-- If `f` is antitone on `(a,b]` and monotone on `[b,c)` then `f` has
a local minimum at `b`. -/
lemma isLocalMin_of_anti_mono.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b :=
  Filter.mem_of_superset (Ioo_mem_nhds g₀ g₁) (fun x hx => by rcases le_total x b  <;> aesop)

/-- Obtain a "predictably-sided" neighborhood of `b` from two one-sided neighborhoods. -/
theorem nhds_of_Ici_Iic.{u} {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [NoMinOrder α] [NoMaxOrder α] {b : α}
    {L : Set α} (hL : L ∈ 𝓝[≤] b)
    {R : Set α} (hR : R ∈ 𝓝[≥] b) : L ∩ Iic b ∪ R ∩ Ici b ∈ 𝓝 b :=
  mem_nhds_iff.mpr (by
  obtain ⟨l,hl⟩ := mem_nhdsWithin_Iic_iff_exists_Ioc_subset.mp hL
  obtain ⟨r,hr⟩ := mem_nhdsWithin_Ici_iff_exists_Ico_subset.mp hR
  use Ioo l r
  exact ⟨ (fun x hx => (le_total x b).elim
      (fun H => Or.inl ⟨hl.2 ⟨hx.1, H⟩, H⟩)
      (fun H => Or.inr ⟨hr.2 ⟨H, hx.2⟩, H⟩)), ⟨isOpen_Ioo, hl.1, hr.1⟩⟩
  )
/-- If `f` is monotone to the left and antitone to the right, then it has a local maximum. -/
lemma isLocalMax_of_mono_anti'.{u, v} {α : Type u} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [NoMinOrder α] [NoMaxOrder α] {β : Type v} [Preorder β] {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : MonotoneOn f a) (h₁ : AntitoneOn f c) : IsLocalMax f b :=
  have : b ∈ a := mem_of_mem_nhdsWithin (by simp) ha
  have : b ∈ c := mem_of_mem_nhdsWithin (by simp) hc
  Filter.mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

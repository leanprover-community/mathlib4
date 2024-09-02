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
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b := by
  apply Filter.mem_of_superset (Ioo_mem_nhds g₀ g₁)
  intro x hx
  rcases le_total x b with hx' | hx' <;> aesop

/-- Each element `b` belongs to `𝓝[≤] b`. -/
theorem mem_nhds_self_le.{u} {α : Type u} [TopologicalSpace α] [LinearOrder α] {b : α}
    {a : Set α} (ha : a ∈ 𝓝[≤] b) : b ∈ a := by
  rw [mem_nhdsWithin] at ha
  obtain ⟨u,hu⟩ := ha
  apply hu.2.2
  simp
  tauto

/-- Each element `b` belongs to `𝓝[≥] b`. -/
theorem mem_nhds_self_ge.{u} {α : Type u} [TopologicalSpace α] [LinearOrder α] {b : α}
    {a : Set α} (ha : a ∈ 𝓝[≥] b) : b ∈ a := by
  rw [mem_nhdsWithin] at ha
  obtain ⟨u,hu⟩ := ha
  apply hu.2.2
  simp
  tauto

/-- Obtain a "predictably-sided" neighborhood of `b` from two one-sided neighborhoods. -/
theorem nhds_of_Ici_Iic.{v, u} {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [NoMinOrder α] [NoMaxOrder α] {β : Type v} [Preorder β] {b : α}
    {a : Set α} (ha : a ∈ 𝓝[≤] b)
    {c : Set α} (hc : c ∈ 𝓝[≥] b) : a ∩ Iic b ∪ c ∩ Ici b ∈ 𝓝 b := by
  rw [mem_nhdsWithin_Iic_iff_exists_Ioc_subset] at ha
  rw [mem_nhdsWithin_Ici_iff_exists_Ico_subset] at hc
  rw [mem_nhds_iff]
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hc
  use Ioo x y
  constructor
  · intro z hz
    by_cases H : z ≤ b
    · left
      constructor
      exact hx.2 <| ⟨hz.1, H⟩
      exact H
    · right
      constructor
      exact hy.2 <| ⟨(le_of_not_ge H), hz.2⟩
      exact le_of_not_ge H
  constructor
  · exact isOpen_Ioo
  tauto

/-- If `f` is monotone to the left and antitone to the right, then it has a local maximum. -/
lemma isLocalMax_of_mono_anti'.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [NoMinOrder α] [NoMaxOrder α]
    [OrderClosedTopology α]
    {β : Type v} [Preorder β]
    {b : α} {f : α → β}
    {a : Set α} (ha : a ∈ 𝓝[≤] b)
    {c : Set α} (hc : c ∈ 𝓝[≥] b)
    (h₀ : MonotoneOn f a)
    (h₁ : AntitoneOn f c) : IsLocalMax f b := by
  unfold IsLocalMax IsMaxFilter Filter.Eventually
  have : (a ∩ Set.Iic b) ∪ (c ∩ Set.Ici b) ∈ 𝓝 b := by
    exact @nhds_of_Ici_Iic α _ _ _ _ _ β _ b a ha c hc
  apply Filter.mem_of_superset this
  intro x hx
  rcases le_total x b with hx' | hx' <;> aesop
  apply h₀
  · exact h
  · exact mem_nhds_self_le ha
  · exact hx'
  apply h₀
  · have : x = b := by apply le_antisymm;tauto;tauto
    subst this
    exact mem_nhds_self_le ha
  · exact mem_nhds_self_le ha
  · exact hx'
  · have : x = b := by apply le_antisymm;tauto;tauto
    subst this
    simp
  · exact h₁ (mem_nhds_self_ge hc) h_1 hx'

/-- If `f` is antitone on `(a,b]` and monotone on `[b,c)` then `f` has
a local minimum at `b`. -/
lemma isLocalMin_of_anti_mono.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b))
    (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b := by

  apply Filter.mem_of_superset (Ioo_mem_nhds g₀ g₁)
  intro x hx
  rcases le_total x b with hx' | hx' <;> aesop

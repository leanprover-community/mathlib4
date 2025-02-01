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
lemma isLocalMax_of_mono_anti
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b :=
  isLocalMax_of_mono_anti' (Ioc_mem_nhdsLE g₀) (Ico_mem_nhdsGE g₁) h₀ h₁

/-- If `f` is antitone on `(a,b]` and monotone on `[b,c)` then `f` has
a local minimum at `b`. -/
lemma isLocalMin_of_anti_mono
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type*} [Preorder β] {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : AntitoneOn f (Ioc a b)) (h₁ : MonotoneOn f (Ico b c)) : IsLocalMin f b :=
  mem_of_superset (Ioo_mem_nhds g₀ g₁) (fun x hx => by rcases le_total x b <;> aesop)
